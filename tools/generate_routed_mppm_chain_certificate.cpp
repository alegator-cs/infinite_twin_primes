#include <algorithm>
#include <array>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <random>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

using u64 = unsigned long long;
using u128 = __uint128_t;

namespace fs = std::filesystem;

namespace {

u64 mod_mul(u64 a, u64 b, u64 m) {
  return (u128)a * b % m;
}

u64 mod_pow(u64 a, u64 e, u64 m) {
  u64 r = 1 % m;
  while (e) {
    if (e & 1) r = mod_mul(r, a, m);
    a = mod_mul(a, a, m);
    e >>= 1;
  }
  return r;
}

bool is_prime(u64 n) {
  if (n < 2) return false;
  static const u64 small[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
  for (u64 p : small) {
    if (n % p == 0) return n == p;
  }
  u64 d = n - 1, s = 0;
  while ((d & 1) == 0) {
    d >>= 1;
    ++s;
  }
  static const u64 bases[] = {2ULL, 325ULL, 9375ULL, 28178ULL, 450775ULL,
                              9780504ULL, 1795265022ULL};
  for (u64 a : bases) {
    if (a % n == 0) continue;
    u64 x = mod_pow(a, d, n);
    if (x == 1 || x == n - 1) continue;
    bool ok = false;
    for (u64 r = 1; r < s; ++r) {
      x = mod_mul(x, x, n);
      if (x == n - 1) {
        ok = true;
        break;
      }
    }
    if (!ok) return false;
  }
  return true;
}

std::mt19937_64 rng(1);

u64 pollard(u64 n) {
  if (n % 2 == 0) return 2;
  if (n % 3 == 0) return 3;
  while (true) {
    u64 c = std::uniform_int_distribution<u64>(1, n - 1)(rng);
    u64 x = std::uniform_int_distribution<u64>(0, n - 1)(rng);
    u64 y = x, d = 1;
    auto f = [&](u64 v) { return (mod_mul(v, v, n) + c) % n; };
    for (int iter = 0; iter < 8000; ++iter) {
      x = f(x);
      y = f(f(y));
      u64 diff = x > y ? x - y : y - x;
      d = std::gcd(diff, n);
      if (d == n) break;
      if (d > 1) return d;
    }
  }
}

std::unordered_map<u64, std::vector<u64>> factor_cache;

std::vector<u64> factor_rec(u64 n) {
  auto it = factor_cache.find(n);
  if (it != factor_cache.end()) return it->second;
  std::vector<u64> out;
  if (n <= 1) {
  } else if (is_prime(n)) {
    out.push_back(n);
  } else {
    u64 d = pollard(n);
    auto a = factor_rec(d);
    auto b = factor_rec(n / d);
    out.insert(out.end(), a.begin(), a.end());
    out.insert(out.end(), b.begin(), b.end());
    std::sort(out.begin(), out.end());
  }
  factor_cache.emplace(n, out);
  return out;
}

bool leg5(u64 p) {
  return p > 5 && mod_pow(5 % p, (p - 1) / 2, p) == 1;
}

std::vector<u64> sqrt5_mod_prime(u64 p) {
  std::vector<u64> none;
  if (!leg5(p)) return none;
  if (p % 4 == 3) {
    u64 r = mod_pow(5, (p + 1) / 4, p);
    std::vector<u64> v = {r, (p - r) % p};
    std::sort(v.begin(), v.end());
    v.erase(std::unique(v.begin(), v.end()), v.end());
    return v;
  }
  u64 q = p - 1, s = 0;
  while ((q & 1) == 0) {
    q >>= 1;
    ++s;
  }
  u64 z = 2;
  while (mod_pow(z, (p - 1) / 2, p) != p - 1) ++z;
  u64 m = s;
  u64 c = mod_pow(z, q, p);
  u64 t = mod_pow(5, q, p);
  u64 r = mod_pow(5, (q + 1) / 2, p);
  while (t != 1) {
    u64 i = 1, tt = mod_mul(t, t, p);
    while (tt != 1) {
      tt = mod_mul(tt, tt, p);
      ++i;
    }
    u64 b = mod_pow(c, 1ULL << (m - i - 1), p);
    m = i;
    c = mod_mul(b, b, p);
    t = mod_mul(t, c, p);
    r = mod_mul(r, b, p);
  }
  std::vector<u64> v = {r, (p - r) % p};
  std::sort(v.begin(), v.end());
  v.erase(std::unique(v.begin(), v.end()), v.end());
  return v;
}

struct Row {
  int typ = 0;  // 0 = left, 1 = right
  u64 u = 0;
  u64 h = 0;
  std::array<u64, 5> vals{};
};

std::unordered_map<u64, std::vector<Row>> rows_cache;

std::vector<Row> rows_for(u64 p) {
  auto it = rows_cache.find(p);
  if (it != rows_cache.end()) return it->second;
  std::vector<Row> out;
  if (!leg5(p)) {
    rows_cache.emplace(p, out);
    return out;
  }
  u64 inv2 = (p + 1) / 2;
  for (u64 s : sqrt5_mod_prime(p)) {
    for (auto [typ, c] : std::vector<std::pair<int, u64>>{{1, 5}, {0, 3}}) {
      u64 u = ((p + s + p - (c % p)) % p);
      u = mod_mul(u, inv2, p);
      u128 mid = (typ == 1)
                     ? ((u128)(u + 1) * (u + 4) + 1)
                     : ((u128)u * (u + 3) + 1);
      if (mid % p != 0) continue;
      u64 h = (u64)(mid / p);
      if (1 <= h && h < p) {
        out.push_back(Row{typ, u, h, {u, u + 1, u + 2, u + 3, u + 4}});
      }
    }
  }
  rows_cache.emplace(p, out);
  return out;
}

std::size_t find_matching_bracket(const std::string& s, std::size_t open) {
  int depth = 0;
  for (std::size_t i = open; i < s.size(); ++i) {
    if (s[i] == '[') ++depth;
    if (s[i] == ']') {
      --depth;
      if (depth == 0) return i;
    }
  }
  throw std::runtime_error("unmatched JSON array");
}

std::vector<u64> parse_array(const std::string& s, const std::string& key) {
  std::size_t pos = s.find("\"" + key + "\"");
  if (pos == std::string::npos) throw std::runtime_error("missing key " + key);
  std::size_t open = s.find('[', pos);
  std::size_t close = find_matching_bracket(s, open);
  std::vector<u64> out;
  u64 val = 0;
  bool in = false;
  for (std::size_t i = open + 1; i < close; ++i) {
    char ch = s[i];
    if ('0' <= ch && ch <= '9') {
      val = val * 10 + (ch - '0');
      in = true;
    } else if (in) {
      out.push_back(val);
      val = 0;
      in = false;
    }
  }
  if (in) out.push_back(val);
  return out;
}

u64 parse_scalar(const std::string& s, const std::string& key) {
  std::size_t pos = s.find("\"" + key + "\"");
  if (pos == std::string::npos) throw std::runtime_error("missing key " + key);
  pos = s.find(':', pos);
  while (pos < s.size() && !std::isdigit((unsigned char)s[pos])) ++pos;
  u64 val = 0;
  while (pos < s.size() && std::isdigit((unsigned char)s[pos])) {
    val = val * 10 + (s[pos] - '0');
    ++pos;
  }
  return val;
}

u64 encode_event(u64 u, int side) {
  return (u << 1) | (u64)side;
}

struct CertData {
  u64 X = 0;
  std::unordered_set<u64> actualEvents;
  std::unordered_map<u64, int> predictedEventId;
  std::vector<u64> predictedCodes;
};

CertData load_cert(const std::string& path) {
  std::ifstream in(path);
  if (!in) throw std::runtime_error("cannot open certificate " + path);
  std::string s((std::istreambuf_iterator<char>(in)), {});
  CertData c;
  c.X = parse_scalar(s, "X");
  auto basev = parse_array(s, "base");
  auto mpv = parse_array(s, "mp");
  auto pmv = parse_array(s, "pm");
  for (u64 u : basev) {
    for (int side = 0; side < 2; ++side) {
      u64 code = encode_event(u, side);
      if (!c.predictedEventId.count(code)) {
        c.predictedEventId.emplace(code, (int)c.predictedEventId.size());
        c.predictedCodes.push_back(code);
      }
    }
  }
  for (u64 u : mpv) c.actualEvents.insert(encode_event(u, 0));
  for (u64 u : pmv) c.actualEvents.insert(encode_event(u, 1));
  return c;
}

struct EdgeWitness {
  u64 parent = 0, child = 0, typ = 0, u = 0, h = 0, slot = 0, quotient = 0;
};

struct DirectWitness {
  u64 parent = 0, typ = 0, u = 0, h = 0, k = 0, targetU = 0;
  u64 side = 0, eventId = 0, code = 0;
};

struct ChainWitness {
  u64 eventId = 0, code = 0, actual = 0, start = 0;
  std::vector<EdgeWitness> edges;
  DirectWitness terminal;
};

struct Search {
  CertData cert;
  u64 minChild = 31;
  std::unordered_map<u64, std::vector<int>> target_cache;
  std::unordered_map<u64, std::vector<u64>> child_cache;
  std::unordered_map<u64, std::vector<int>> reach_cache;
  std::unordered_map<u64, std::unordered_map<int, DirectWitness>> direct_cache;
  std::unordered_map<u64, EdgeWitness> edge_cache;

  std::vector<int> target_events_at(u64 p) {
    auto it = target_cache.find(p);
    if (it != target_cache.end()) return it->second;
    std::vector<int> ev;
    for (const Row& r : rows_for(p)) {
      if (p < cert.X) {
        for (u64 u = r.u; u < cert.X; u += p) {
          auto im = cert.predictedEventId.find(encode_event(u, 0));
          if (im != cert.predictedEventId.end()) ev.push_back(im->second);
          auto ip = cert.predictedEventId.find(encode_event(u, 1));
          if (ip != cert.predictedEventId.end()) ev.push_back(ip->second);
        }
      } else if (r.u < cert.X) {
        auto im = cert.predictedEventId.find(encode_event(r.u, 0));
        if (im != cert.predictedEventId.end()) ev.push_back(im->second);
        auto ip = cert.predictedEventId.find(encode_event(r.u, 1));
        if (ip != cert.predictedEventId.end()) ev.push_back(ip->second);
      }
    }
    std::sort(ev.begin(), ev.end());
    ev.erase(std::unique(ev.begin(), ev.end()), ev.end());
    target_cache.emplace(p, ev);
    return ev;
  }

  std::vector<u64> child_edges(u64 p) {
    auto it = child_cache.find(p);
    if (it != child_cache.end()) return it->second;
    std::vector<u64> out;
    for (const Row& r : rows_for(p)) {
      for (u64 v : r.vals) {
        auto fs = factor_rec(v);
        for (u64 q : fs) {
          if (minChild <= q && q < p && leg5(q)) out.push_back(q);
        }
      }
    }
    std::sort(out.begin(), out.end(), std::greater<u64>());
    out.erase(std::unique(out.begin(), out.end()), out.end());
    child_cache.emplace(p, out);
    return out;
  }

  std::vector<int> reachable_events(u64 p) {
    auto it = reach_cache.find(p);
    if (it != reach_cache.end()) return it->second;
    std::vector<int> ev = target_events_at(p);
    for (u64 q : child_edges(p)) {
      auto child = reachable_events(q);
      ev.insert(ev.end(), child.begin(), child.end());
    }
    std::sort(ev.begin(), ev.end());
    ev.erase(std::unique(ev.begin(), ev.end()), ev.end());
    reach_cache.emplace(p, ev);
    return ev;
  }

  const std::unordered_map<int, DirectWitness>& direct_witnesses_at(u64 p) {
    auto cached = direct_cache.find(p);
    if (cached != direct_cache.end()) return cached->second;
    std::unordered_map<int, DirectWitness> out;
    for (const Row& r : rows_for(p)) {
      if (p < cert.X) {
        for (u64 targetU = r.u, k = 0; targetU < cert.X; targetU += p, ++k) {
          for (u64 side = 0; side < 2; ++side) {
            u64 code = encode_event(targetU, (int)side);
            auto it = cert.predictedEventId.find(code);
            if (it != cert.predictedEventId.end()) {
              out.emplace(it->second,
                          DirectWitness{p, (u64)r.typ, r.u, r.h, k, targetU,
                                        side, (u64)it->second, code});
            }
          }
        }
      } else if (r.u < cert.X) {
        for (u64 side = 0; side < 2; ++side) {
          u64 code = encode_event(r.u, (int)side);
          auto it = cert.predictedEventId.find(code);
          if (it != cert.predictedEventId.end()) {
            out.emplace(it->second,
                        DirectWitness{p, (u64)r.typ, r.u, r.h, 0, r.u,
                                      side, (u64)it->second, code});
          }
        }
      }
    }
    auto inserted = direct_cache.emplace(p, std::move(out));
    return inserted.first->second;
  }

  DirectWitness direct_witness(u64 p, int id) {
    const auto& table = direct_witnesses_at(p);
    auto it = table.find(id);
    if (it != table.end()) return it->second;
    throw std::runtime_error("missing direct witness");
  }

  EdgeWitness edge_witness(u64 p, u64 q) {
    u64 key = (p << 32) ^ q;
    auto cached = edge_cache.find(key);
    if (cached != edge_cache.end()) return cached->second;
    for (const Row& r : rows_for(p)) {
      for (u64 slot = 0; slot < 5; ++slot) {
        u64 v = r.vals[(std::size_t)slot];
        if (v % q == 0) {
          auto fs = factor_rec(v);
          if (std::find(fs.begin(), fs.end(), q) != fs.end() &&
              minChild <= q && q < p && leg5(q)) {
            EdgeWitness edge{p, q, (u64)r.typ, r.u, r.h, slot, v / q};
            edge_cache.emplace(key, edge);
            return edge;
          }
        }
      }
    }
    throw std::runtime_error("missing edge witness");
  }

  ChainWitness chain_witness(u64 p, int id, u64 start) {
    auto direct = target_events_at(p);
    if (std::binary_search(direct.begin(), direct.end(), id)) {
      u64 code = cert.predictedCodes[(std::size_t)id];
      return ChainWitness{(u64)id, code,
                          cert.actualEvents.count(code) ? 1ULL : 0ULL,
                          start, {}, direct_witness(p, id)};
    }
    for (u64 q : child_edges(p)) {
      auto childReach = reachable_events(q);
      if (std::binary_search(childReach.begin(), childReach.end(), id)) {
        ChainWitness child = chain_witness(q, id, start);
        child.edges.insert(child.edges.begin(), edge_witness(p, q));
        return child;
      }
    }
    throw std::runtime_error("missing chain witness");
  }
};

struct Options {
  std::string cert = "certificates/generated_mppm_pressure_certificate.json";
  std::string out_dir = "TwinPrimeCertificate/GeneratedRoutedMPPMChains";
  u64 start = 191281;
  std::size_t shard_size = 250;
  std::size_t limit = 0;
};

u64 parse_u64(const std::string& s) {
  std::size_t pos = 0;
  u64 v = std::stoull(s, &pos);
  if (pos != s.size()) throw std::runtime_error("bad integer: " + s);
  return v;
}

Options parse_options(int argc, char** argv) {
  Options opt;
  for (int i = 1; i < argc; ++i) {
    std::string a = argv[i];
    auto need = [&]() -> std::string {
      if (++i >= argc) throw std::runtime_error("missing value after " + a);
      return argv[i];
    };
    if (a == "--cert") opt.cert = need();
    else if (a == "--out-dir") opt.out_dir = need();
    else if (a == "--start") opt.start = parse_u64(need());
    else if (a == "--shard-size") opt.shard_size = (std::size_t)parse_u64(need());
    else if (a == "--limit") opt.limit = (std::size_t)parse_u64(need());
    else throw std::runtime_error("unknown argument: " + a);
  }
  if (opt.shard_size == 0) throw std::runtime_error("--shard-size must be positive");
  return opt;
}

std::string shard_name(std::size_t i) {
  std::ostringstream ss;
  ss << "Shard" << std::setw(3) << std::setfill('0') << i;
  return ss.str();
}

void write_edge(std::ostream& out, const EdgeWitness& e) {
  out << "{ parent := " << e.parent
      << ", child := " << e.child
      << ", typ := " << e.typ
      << ", u := " << e.u
      << ", h := " << e.h
      << ", slot := " << e.slot
      << ", quotient := " << e.quotient << " }";
}

void write_direct(std::ostream& out, const DirectWitness& w) {
  out << "{ parent := " << w.parent
      << ", typ := " << w.typ
      << ", u := " << w.u
      << ", h := " << w.h
      << ", k := " << w.k
      << ", targetU := " << w.targetU
      << ", side := " << w.side
      << ", eventId := " << w.eventId
      << ", code := " << w.code << " }";
}

void write_chain(std::ostream& out, const ChainWitness& c) {
  out << "{ eventId := " << c.eventId
      << ", code := " << c.code
      << ", actual := " << c.actual
      << ", start := " << c.start
      << ", edges := [";
  for (std::size_t i = 0; i < c.edges.size(); ++i) {
    if (i) out << ", ";
    write_edge(out, c.edges[i]);
  }
  out << "], terminal := ";
  write_direct(out, c.terminal);
  out << " }";
}

void write_shard(const fs::path& path, const std::string& mod,
                 const std::vector<ChainWitness>& chains,
                 std::size_t lo, std::size_t hi) {
  std::ofstream out(path);
  if (!out) throw std::runtime_error("could not write " + path.string());
  u64 actual = 0;
  for (std::size_t i = lo; i < hi; ++i) actual += chains[i].actual;
  u64 falseCount = (u64)(hi - lo) - actual;
  out << "import TwinPrimeCertificate.RoutedMPPMChainCertificate\n\n";
  out << "set_option maxRecDepth 20000\n\n";
  out << "namespace TwinPrimeCertificate.GeneratedRoutedMPPMChains." << mod << "\n\n";
  out << "open TwinPrimeCertificate.RoutedMPPMChainCertificate\n\n";
  out << "def chains : List ChainWitness :=\n  [";
  for (std::size_t i = lo; i < hi; ++i) {
    if (i != lo) out << ",\n   ";
    write_chain(out, chains[i]);
  }
  out << "]\n\n";
  out << "def chainCount : Nat := " << (hi - lo) << "\n";
  out << "def actualPredictedCount : Nat := " << actual << "\n";
  out << "def falsePredictedCount : Nat := " << falseCount << "\n";
  out << "def firstId : Nat := " << chains[lo].eventId << "\n";
  out << "def lastId : Nat := " << chains[hi - 1].eventId << "\n\n";
  out << "theorem chains_length : chains.length = chainCount := by\n";
  out << "  native_decide\n\n";
  out << "theorem chains_valid : allValid chains = true := by\n";
  out << "  native_decide\n\n";
  out << "theorem chains_strictlyIncreasing : strictlyIncreasingIds chains = true := by\n";
  out << "  native_decide\n\n";
  out << "theorem actualCount_eq : actualCount chains = actualPredictedCount := by\n";
  out << "  native_decide\n\n";
  out << "theorem falseCount_eq : falseCount chains = falsePredictedCount := by\n";
  out << "  native_decide\n\n";
  out << "end TwinPrimeCertificate.GeneratedRoutedMPPMChains." << mod << "\n";
}

void write_index(const fs::path& path, std::size_t shard_count,
                 const std::vector<ChainWitness>& chains) {
  std::ofstream out(path);
  if (!out) throw std::runtime_error("could not write index");
  for (std::size_t i = 0; i < shard_count; ++i) {
    out << "import TwinPrimeCertificate.GeneratedRoutedMPPMChains." << shard_name(i) << "\n";
  }
  out << "\n/-!\n# Generated Routed MP/PM Chain Certificate\n\n";
  out << "Each shard checks explicit recursive descent witnesses for predicted events.\n";
  out << "-/\n\n";
  out << "namespace TwinPrimeCertificate.GeneratedRoutedMPPMChains\n\n";
  out << "def shardCount : Nat := " << shard_count << "\n";
  out << "def checkedChainCount : Nat :=\n  ";
  for (std::size_t i = 0; i < shard_count; ++i) {
    if (i) out << " +\n  ";
    out << shard_name(i) << ".chainCount";
  }
  out << "\n\n";
  out << "def checkedActualPredictedCount : Nat :=\n  ";
  for (std::size_t i = 0; i < shard_count; ++i) {
    if (i) out << " +\n  ";
    out << shard_name(i) << ".actualPredictedCount";
  }
  out << "\n\n";
  out << "def checkedFalsePredictedCount : Nat :=\n  ";
  for (std::size_t i = 0; i < shard_count; ++i) {
    if (i) out << " +\n  ";
    out << shard_name(i) << ".falsePredictedCount";
  }
  out << "\n\n";
  out << "theorem checkedChainCount_eq : checkedChainCount = " << chains.size() << " := by\n";
  out << "  norm_num [checkedChainCount";
  for (std::size_t i = 0; i < shard_count; ++i) out << ", " << shard_name(i) << ".chainCount";
  out << "]\n\n";
  u64 actual = 0;
  for (const auto& c : chains) actual += c.actual;
  out << "theorem checkedActualPredictedCount_eq : checkedActualPredictedCount = " << actual << " := by\n";
  out << "  norm_num [checkedActualPredictedCount";
  for (std::size_t i = 0; i < shard_count; ++i) out << ", " << shard_name(i) << ".actualPredictedCount";
  out << "]\n\n";
  out << "theorem checkedFalsePredictedCount_eq : checkedFalsePredictedCount = "
      << (chains.size() - actual) << " := by\n";
  out << "  norm_num [checkedFalsePredictedCount";
  for (std::size_t i = 0; i < shard_count; ++i) out << ", " << shard_name(i) << ".falsePredictedCount";
  out << "]\n\n";
  out << "theorem shard_boundaries_strict :\n    True";
  for (std::size_t i = 1; i < shard_count; ++i) {
    out << " /\\ " << shard_name(i - 1) << ".lastId < " << shard_name(i) << ".firstId";
  }
  out << " := by\n";
  out << "  norm_num [";
  for (std::size_t i = 0; i < shard_count; ++i) {
    if (i) out << ", ";
    out << shard_name(i) << ".firstId, " << shard_name(i) << ".lastId";
  }
  out << "]\n\n";
  out << "end TwinPrimeCertificate.GeneratedRoutedMPPMChains\n";
}

}  // namespace

int main(int argc, char** argv) {
  try {
    Options opt = parse_options(argc, argv);
    Search search;
    search.cert = load_cert(opt.cert);
    std::vector<int> eventIds = search.reachable_events(opt.start);
    if (opt.limit && eventIds.size() > opt.limit) eventIds.resize(opt.limit);
    std::vector<ChainWitness> chains;
    chains.reserve(eventIds.size());
    for (int id : eventIds) chains.push_back(search.chain_witness(opt.start, id, opt.start));
    std::sort(chains.begin(), chains.end(),
              [](const ChainWitness& a, const ChainWitness& b) {
                return a.eventId < b.eventId;
              });

    fs::remove_all(opt.out_dir);
    fs::create_directories(opt.out_dir);
    const std::size_t shard_count =
        (chains.size() + opt.shard_size - 1) / opt.shard_size;
    for (std::size_t s = 0; s < shard_count; ++s) {
      std::size_t lo = s * opt.shard_size;
      std::size_t hi = std::min(chains.size(), lo + opt.shard_size);
      write_shard(fs::path(opt.out_dir) / (shard_name(s) + ".lean"),
                  shard_name(s), chains, lo, hi);
    }
    write_index(fs::path(opt.out_dir) / "Index.lean", shard_count, chains);

    u64 actual = 0, maxDepth = 0;
    for (const auto& c : chains) {
      actual += c.actual;
      maxDepth = std::max<u64>(maxDepth, c.edges.size());
    }
    std::cout << "{\n";
    std::cout << "  \"mode\": \"routed-mppm-chain-certificate\",\n";
    std::cout << "  \"chains\": " << chains.size() << ",\n";
    std::cout << "  \"actualPredicted\": " << actual << ",\n";
    std::cout << "  \"falsePredicted\": " << (chains.size() - actual) << ",\n";
    std::cout << "  \"maxDepth\": " << maxDepth << ",\n";
    std::cout << "  \"shards\": " << shard_count << "\n";
    std::cout << "}\n";
  } catch (const std::exception& ex) {
    std::cerr << ex.what() << "\n";
    return 1;
  }
  return 0;
}

