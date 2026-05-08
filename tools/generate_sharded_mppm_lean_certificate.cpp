#include <algorithm>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using u64 = unsigned long long;

namespace fs = std::filesystem;

namespace {

struct Event {
  u64 id;
  u64 code;
  u64 actual;
};

struct Interval {
  u64 lo;
  u64 hi;
};

struct Options {
  std::string csv = "certificates/generated_mppm_overflow_events.csv";
  std::string out_dir = "TwinPrimeExternal/GeneratedShardedMPPM";
  std::size_t shard_size = 500;
  u64 actual_cap = 95568;
  u64 expected_predicted = 181052;
  u64 expected_actual_predicted = 65419;
  u64 expected_false_predicted = 115633;
};

u64 parse_u64(const std::string& s, const std::string& name) {
  std::size_t pos = 0;
  u64 value = std::stoull(s, &pos);
  if (pos != s.size()) throw std::runtime_error("invalid integer for " + name);
  return value;
}

Options parse_options(int argc, char** argv) {
  Options opt;
  for (int i = 1; i < argc; ++i) {
    const std::string arg = argv[i];
    auto need = [&]() -> std::string {
      if (++i >= argc) throw std::runtime_error("missing value after " + arg);
      return argv[i];
    };
    if (arg == "--csv") opt.csv = need();
    else if (arg == "--out-dir") opt.out_dir = need();
    else if (arg == "--shard-size") opt.shard_size = parse_u64(need(), arg);
    else if (arg == "--actual-cap") opt.actual_cap = parse_u64(need(), arg);
    else if (arg == "--expected-predicted") opt.expected_predicted = parse_u64(need(), arg);
    else if (arg == "--expected-actual-predicted") opt.expected_actual_predicted = parse_u64(need(), arg);
    else if (arg == "--expected-false-predicted") opt.expected_false_predicted = parse_u64(need(), arg);
    else throw std::runtime_error("unknown argument: " + arg);
  }
  if (opt.shard_size == 0) throw std::runtime_error("--shard-size must be positive");
  return opt;
}

std::vector<Event> read_events(const std::string& path) {
  std::ifstream in(path);
  if (!in) throw std::runtime_error("could not open event CSV: " + path);
  std::vector<Event> events;
  std::string line;
  while (std::getline(in, line)) {
    if (line.empty()) continue;
    std::stringstream ss(line);
    std::string a, b, c;
    if (!std::getline(ss, a, ',') ||
        !std::getline(ss, b, ',') ||
        !std::getline(ss, c, ',')) {
      throw std::runtime_error("bad CSV line: " + line);
    }
    Event ev{parse_u64(a, "id"), parse_u64(b, "code"), parse_u64(c, "actual")};
    if (ev.actual > 1) throw std::runtime_error("actual flag is not 0/1");
    events.push_back(ev);
  }
  std::sort(events.begin(), events.end(),
            [](const Event& x, const Event& y) { return x.id < y.id; });
  for (std::size_t i = 1; i < events.size(); ++i) {
    if (events[i - 1].id == events[i].id) {
      throw std::runtime_error("duplicate event id");
    }
  }
  return events;
}

std::vector<Interval> compress_intervals(const std::vector<Event>& events) {
  std::vector<Interval> intervals;
  if (events.empty()) return intervals;
  u64 lo = events.front().id;
  u64 hi = lo;
  for (std::size_t i = 1; i < events.size(); ++i) {
    if (events[i].id == hi + 1) {
      hi = events[i].id;
    } else {
      intervals.push_back({lo, hi});
      lo = hi = events[i].id;
    }
  }
  intervals.push_back({lo, hi});
  return intervals;
}

std::string shard_name(std::size_t i) {
  std::ostringstream ss;
  ss << "Shard" << std::setw(3) << std::setfill('0') << i;
  return ss.str();
}

u64 interval_count(const std::vector<Interval>& intervals,
                   std::size_t lo, std::size_t hi) {
  u64 count = 0;
  for (std::size_t i = lo; i < hi; ++i) count += intervals[i].hi - intervals[i].lo + 1;
  return count;
}

void write_interval_list(std::ostream& out, const std::vector<Interval>& intervals,
                         std::size_t lo, std::size_t hi) {
  out << "[";
  for (std::size_t i = lo; i < hi; ++i) {
    if (i != lo) out << ", ";
    out << "(" << intervals[i].lo << ", " << intervals[i].hi << ")";
  }
  out << "]";
}

void write_shard(const fs::path& path, const std::string& mod_name,
                 const std::vector<Interval>& intervals,
                 std::size_t lo, std::size_t hi) {
  std::ofstream out(path);
  if (!out) throw std::runtime_error("could not write shard " + path.string());
  const u64 count = interval_count(intervals, lo, hi);
  out << "import TwinPrimeExternal.ShardedMPPMCertificate\n\n";
  out << "set_option maxRecDepth 20000\n\n";
  out << "namespace TwinPrimeExternal.GeneratedShardedMPPM." << mod_name << "\n\n";
  out << "def intervals : List (Nat × Nat) :=\n  ";
  write_interval_list(out, intervals, lo, hi);
  out << "\n\n";
  out << "def intervalCount : Nat := " << (hi - lo) << "\n";
  out << "def checkedEventCount : Nat := " << count << "\n";
  out << "def firstId : Nat := " << intervals[lo].lo << "\n";
  out << "def lastId : Nat := " << intervals[hi - 1].hi << "\n\n";
  out << "theorem intervals_length : intervals.length = intervalCount := by\n";
  out << "  native_decide\n\n";
  out << "theorem intervals_valid :\n";
  out << "    intervals.all (fun p => p.1 <= p.2) = true := by\n";
  out << "  native_decide\n\n";
  out << "theorem intervals_strictlySeparated :\n";
  out << "    intervals.Pairwise (fun a b => a.2 < b.1) := by\n";
  out << "  native_decide\n\n";
  out << "theorem checkedEventCount_eq_sum :\n";
  out << "    (intervals.map TwinPrimeExternal.ShardedMPPMCertificate.intervalLength).sum =\n";
  out << "      checkedEventCount := by\n";
  out << "  native_decide\n\n";
  out << "end TwinPrimeExternal.GeneratedShardedMPPM." << mod_name << "\n";
}

void write_index(const fs::path& path, std::size_t shard_count,
                 const Options& opt) {
  std::ofstream out(path);
  if (!out) throw std::runtime_error("could not write index");
  for (std::size_t i = 0; i < shard_count; ++i) {
    out << "import TwinPrimeExternal.GeneratedShardedMPPM." << shard_name(i) << "\n";
  }
  out << "\n/-!\n# Generated Sharded MP/PM Overflow Certificate\n\n";
  out << "This manifest imports interval shards for the generated overflow event IDs.\n";
  out << "Lean checks each interval shard independently and checks the global count\n";
  out << "arithmetic here.\n-/\n\n";
  out << "namespace TwinPrimeExternal.GeneratedShardedMPPM\n\n";
  out << "def shardCount : Nat := " << shard_count << "\n";
  out << "def actualCap : Nat := " << opt.actual_cap << "\n";
  out << "def expectedPredictedCount : Nat := " << opt.expected_predicted << "\n";
  out << "def expectedActualPredictedCount : Nat := " << opt.expected_actual_predicted << "\n";
  out << "def expectedFalsePredictedCount : Nat := " << opt.expected_false_predicted << "\n\n";
  out << "def checkedPredictedCount : Nat :=\n  ";
  for (std::size_t i = 0; i < shard_count; ++i) {
    if (i) out << " +\n  ";
    out << shard_name(i) << ".checkedEventCount";
  }
  out << "\n\n";
  out << "theorem checkedPredictedCount_eq :\n";
  out << "    checkedPredictedCount = expectedPredictedCount := by\n";
  out << "  norm_num [checkedPredictedCount, expectedPredictedCount";
  for (std::size_t i = 0; i < shard_count; ++i) {
    out << ", " << shard_name(i) << ".checkedEventCount";
  }
  out << "]\n\n";
  out << "theorem expectedPredictedCount_eq_core :\n";
  out << "    expectedPredictedCount = TwinPrimeExternal.predictedEventCount := by\n";
  out << "  norm_num [expectedPredictedCount, TwinPrimeExternal.predictedEventCount]\n\n";
  out << "theorem actualCap_eq_core :\n";
  out << "    actualCap = TwinPrimeExternal.generatedMPPMCard := by\n";
  out << "  norm_num [actualCap, TwinPrimeExternal.generatedMPPMCard]\n\n";
  out << "theorem checkedPredictedCount_exceeds_actualCap :\n";
  out << "    actualCap < checkedPredictedCount := by\n";
  out << "  norm_num [actualCap, checkedPredictedCount";
  for (std::size_t i = 0; i < shard_count; ++i) {
    out << ", " << shard_name(i) << ".checkedEventCount";
  }
  out << "]\n\n";
  out << "theorem checkedPredictedCount_exceeds_generatedMPPMCard :\n";
  out << "    TwinPrimeExternal.generatedMPPMCard < checkedPredictedCount := by\n";
  out << "  simpa [actualCap_eq_core] using checkedPredictedCount_exceeds_actualCap\n\n";
  out << "theorem shard_boundaries_strict :\n    True";
  for (std::size_t i = 1; i < shard_count; ++i) {
    out << " /\\ " << shard_name(i - 1) << ".lastId < "
        << shard_name(i) << ".firstId";
  }
  out << " := by\n";
  out << "  norm_num [";
  for (std::size_t i = 0; i < shard_count; ++i) {
    if (i) out << ", ";
    out << shard_name(i) << ".firstId, " << shard_name(i) << ".lastId";
  }
  out << "]\n\n";
  out << "end TwinPrimeExternal.GeneratedShardedMPPM\n";
}

}  // namespace

int main(int argc, char** argv) {
  try {
    const Options opt = parse_options(argc, argv);
    const auto events = read_events(opt.csv);
    u64 actual = 0;
    for (const auto& ev : events) actual += ev.actual;
    const u64 false_count = events.size() - actual;
    if (events.size() != opt.expected_predicted) throw std::runtime_error("predicted count mismatch");
    if (actual != opt.expected_actual_predicted) throw std::runtime_error("actual-predicted count mismatch");
    if (false_count != opt.expected_false_predicted) throw std::runtime_error("false-predicted count mismatch");

    const auto intervals = compress_intervals(events);
    fs::remove_all(opt.out_dir);
    fs::create_directories(opt.out_dir);
    const std::size_t shard_count =
        (intervals.size() + opt.shard_size - 1) / opt.shard_size;
    for (std::size_t s = 0; s < shard_count; ++s) {
      const std::size_t lo = s * opt.shard_size;
      const std::size_t hi = std::min(intervals.size(), lo + opt.shard_size);
      write_shard(fs::path(opt.out_dir) / (shard_name(s) + ".lean"),
                  shard_name(s), intervals, lo, hi);
    }
    write_index(fs::path(opt.out_dir) / "Index.lean", shard_count, opt);

    std::cout << "{\n";
    std::cout << "  \"mode\": \"sharded-mppm-lean-interval-certificate\",\n";
    std::cout << "  \"eventRows\": " << events.size() << ",\n";
    std::cout << "  \"intervals\": " << intervals.size() << ",\n";
    std::cout << "  \"shardSize\": " << opt.shard_size << ",\n";
    std::cout << "  \"shards\": " << shard_count << "\n";
    std::cout << "}\n";
    return 0;
  } catch (const std::exception& ex) {
    std::cerr << "error: " << ex.what() << "\n";
    return 1;
  }
}
