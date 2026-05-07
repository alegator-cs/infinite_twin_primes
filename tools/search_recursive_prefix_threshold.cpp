#include <bits/stdc++.h>
using namespace std;

using u64 = unsigned long long;
using u128 = __uint128_t;

static u64 mod_mul(u64 a, u64 b, u64 m) {
  return (u128)a * b % m;
}

static u64 mod_pow(u64 a, u64 e, u64 m) {
  u64 r = 1 % m;
  while (e) {
    if (e & 1) r = mod_mul(r, a, m);
    a = mod_mul(a, a, m);
    e >>= 1;
  }
  return r;
}

static bool is_prime(u64 n) {
  if (n < 2) return false;
  static const u64 small[] = {2,3,5,7,11,13,17,19,23,29,31,37};
  for (u64 p : small) {
    if (n % p == 0) return n == p;
  }
  u64 d = n - 1, s = 0;
  while ((d & 1) == 0) { d >>= 1; ++s; }
  static const u64 bases[] = {2ULL, 325ULL, 9375ULL, 28178ULL, 450775ULL,
                              9780504ULL, 1795265022ULL};
  for (u64 a : bases) {
    if (a % n == 0) continue;
    u64 x = mod_pow(a, d, n);
    if (x == 1 || x == n - 1) continue;
    bool ok = false;
    for (u64 r = 1; r < s; ++r) {
      x = mod_mul(x, x, n);
      if (x == n - 1) { ok = true; break; }
    }
    if (!ok) return false;
  }
  return true;
}

static mt19937_64 rng(1);

static u64 pollard(u64 n) {
  if (n % 2 == 0) return 2;
  if (n % 3 == 0) return 3;
  while (true) {
    u64 c = uniform_int_distribution<u64>(1, n - 1)(rng);
    u64 x = uniform_int_distribution<u64>(0, n - 1)(rng);
    u64 y = x, d = 1;
    auto f = [&](u64 v) { return (mod_mul(v, v, n) + c) % n; };
    for (int iter = 0; iter < 8000; ++iter) {
      x = f(x);
      y = f(f(y));
      u64 diff = x > y ? x - y : y - x;
      d = gcd(diff, n);
      if (d == n) break;
      if (d > 1) return d;
    }
  }
}

static unordered_map<u64, vector<u64>> factor_cache;

static vector<u64> factor_rec(u64 n) {
  auto it = factor_cache.find(n);
  if (it != factor_cache.end()) return it->second;
  vector<u64> out;
  if (n <= 1) {
  } else if (is_prime(n)) {
    out.push_back(n);
  } else {
    u64 d = pollard(n);
    auto a = factor_rec(d);
    auto b = factor_rec(n / d);
    out.insert(out.end(), a.begin(), a.end());
    out.insert(out.end(), b.begin(), b.end());
    sort(out.begin(), out.end());
  }
  factor_cache.emplace(n, out);
  return out;
}

static bool leg5(u64 p) {
  return p > 5 && mod_pow(5 % p, (p - 1) / 2, p) == 1;
}

static vector<u64> sqrt5_mod_prime(u64 p) {
  vector<u64> none;
  if (!leg5(p)) return none;
  if (p % 4 == 3) {
    u64 r = mod_pow(5, (p + 1) / 4, p);
    vector<u64> v = {r, (p - r) % p};
    sort(v.begin(), v.end());
    v.erase(unique(v.begin(), v.end()), v.end());
    return v;
  }
  u64 q = p - 1, s = 0;
  while ((q & 1) == 0) { q >>= 1; ++s; }
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
  vector<u64> v = {r, (p - r) % p};
  sort(v.begin(), v.end());
  v.erase(unique(v.begin(), v.end()), v.end());
  return v;
}

struct Row {
  char typ;
  u64 u;
  u64 h;
  array<u64,5> vals;
};

static unordered_map<u64, vector<Row>> rows_cache;

static vector<Row> rows_for(u64 p) {
  auto it = rows_cache.find(p);
  if (it != rows_cache.end()) return it->second;
  vector<Row> out;
  if (!leg5(p)) {
    rows_cache.emplace(p, out);
    return out;
  }
  u64 inv2 = (p + 1) / 2;
  for (u64 s : sqrt5_mod_prime(p)) {
    for (auto [typ, c] : vector<pair<char,u64>>{{'R',5},{'L',3}}) {
      u64 u = ((p + s + p - (c % p)) % p);
      u = mod_mul(u, inv2, p);
      u128 mid = (typ == 'R')
        ? ((u128)(u + 1) * (u + 4) + 1)
        : ((u128)u * (u + 3) + 1);
      if (mid % p != 0) continue;
      u64 h = (u64)(mid / p);
      if (1 <= h && h < p) {
        out.push_back(Row{typ, u, h, {u, u+1, u+2, u+3, u+4}});
      }
    }
  }
  rows_cache.emplace(p, out);
  return out;
}

static size_t find_matching_bracket(const string& s, size_t open) {
  int depth = 0;
  for (size_t i = open; i < s.size(); ++i) {
    if (s[i] == '[') ++depth;
    if (s[i] == ']') {
      --depth;
      if (depth == 0) return i;
    }
  }
  throw runtime_error("unmatched JSON array");
}

static vector<u64> parse_array(const string& s, const string& key) {
  size_t pos = s.find("\"" + key + "\"");
  if (pos == string::npos) throw runtime_error("missing key " + key);
  size_t open = s.find('[', pos);
  size_t close = find_matching_bracket(s, open);
  vector<u64> out;
  u64 val = 0;
  bool in = false;
  for (size_t i = open + 1; i < close; ++i) {
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

static u64 parse_scalar(const string& s, const string& key) {
  size_t pos = s.find("\"" + key + "\"");
  if (pos == string::npos) throw runtime_error("missing key " + key);
  pos = s.find(':', pos);
  while (pos < s.size() && !isdigit((unsigned char)s[pos])) ++pos;
  u64 val = 0;
  while (pos < s.size() && isdigit((unsigned char)s[pos])) {
    val = val * 10 + (s[pos] - '0');
    ++pos;
  }
  return val;
}

static u64 encode_event(u64 u, int side) {
  return (u << 1) | (u64)side;
}

struct CertData {
  u64 X = 0;
  u64 actualCap = 0;
  u64 predictedUniverse = 0;
  unordered_set<u64> actualEvents;
  unordered_map<u64,int> predictedEventId;
  vector<u64> predictedCodes;
};

static CertData load_cert(const string& path) {
  ifstream in(path);
  if (!in) throw runtime_error("cannot open certificate " + path);
  string s((istreambuf_iterator<char>(in)), {});
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
  for (u64 u : mpv) {
    u64 code = encode_event(u, 0);
    c.actualEvents.insert(code);
  }
  for (u64 u : pmv) {
    u64 code = encode_event(u, 1);
    c.actualEvents.insert(code);
  }
  c.actualCap = c.actualEvents.size();
  c.predictedUniverse = c.predictedEventId.size();
  return c;
}

struct Search {
  CertData cert;
  u64 minChild = 31;
  unordered_map<u64, vector<int>> target_cache;
  unordered_map<u64, vector<u64>> child_cache;
  unordered_map<u64, vector<int>> reach_cache;
  long long childRowsSeen = 0;
  long long childSlotsSeen = 0;
  long long productiveSlots = 0;
  long long primeProductiveSlots = 0;
  long long compositeProductiveSlots = 0;

  vector<int> target_events_at(u64 p) {
    auto it = target_cache.find(p);
    if (it != target_cache.end()) return it->second;
    vector<int> ev;
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
    sort(ev.begin(), ev.end());
    ev.erase(unique(ev.begin(), ev.end()), ev.end());
    target_cache.emplace(p, ev);
    return ev;
  }

  vector<u64> child_edges(u64 p) {
    auto it = child_cache.find(p);
    if (it != child_cache.end()) return it->second;
    vector<u64> out;
    for (const Row& r : rows_for(p)) {
      ++childRowsSeen;
      for (u64 v : r.vals) {
        ++childSlotsSeen;
        auto fs = factor_rec(v);
        bool productive = false;
        for (u64 q : fs) {
          if (minChild <= q && q < p && leg5(q)) {
            out.push_back(q);
            productive = true;
          }
        }
        if (productive) {
          ++productiveSlots;
          if (is_prime(v)) ++primeProductiveSlots;
          else ++compositeProductiveSlots;
        }
      }
    }
    sort(out.begin(), out.end(), greater<u64>());
    out.erase(unique(out.begin(), out.end()), out.end());
    child_cache.emplace(p, out);
    return out;
  }

  vector<int> reachable_events(u64 p) {
    auto it = reach_cache.find(p);
    if (it != reach_cache.end()) return it->second;
    vector<int> ev = target_events_at(p);
    for (u64 q : child_edges(p)) {
      auto child = reachable_events(q);
      ev.insert(ev.end(), child.begin(), child.end());
    }
    sort(ev.begin(), ev.end());
    ev.erase(unique(ev.begin(), ev.end()), ev.end());
    reach_cache.emplace(p, ev);
    return ev;
  }
};

static void usage(const char* argv0) {
  cerr
    << "usage: " << argv0 << " [options]\n\n"
    << "Options:\n"
    << "  --cert PATH       generated MP/PM JSON certificate\n"
    << "  --rstart N        first candidate root, default 191265\n"
    << "  --max-span N      stop after this integer span if threshold not reached\n"
    << "  --cap N           threshold to exceed; default is generated MP+PM card\n"
    << "  --print-every N   print one JSONL line every N split roots, default 100\n"
    << "  --min-child N     smallest recursively continuing child prime, default 31\n\n"
    << "  --lean-out PATH   write a small Lean count certificate at first overflow\n"
    << "  --json-out PATH   write a JSON count certificate at first overflow\n\n"
    << "The search exhausts recursive quadratic descent depth: each split prime\n"
    << "is routed through all smaller split child primes until the decreasing DAG\n"
    << "bottoms out.  The stopping counter is routedStarts > cap.\n";
}

static void write_lean_certificate(
    const string& path,
    u64 root,
    u64 span,
    u64 predictedCount,
    u64 realCount,
    u64 falsePredicted,
    u64 routedStarts,
    u64 splitRoots) {
  ofstream out(path, ios::binary);
  if (!out) throw runtime_error("cannot open --lean-out " + path);
  out
    << "import TwinPrimeExternal.Core\n\n"
    << "/-!\n"
    << "# Generated External Certificate\n\n"
    << "Generated by `tools/search_recursive_prefix_threshold.cpp`.\n"
    << "Lean checks the displayed arithmetic. The cofinal-tail obstruction is\n"
    << "the external C++ certificate boundary: the C++ search and its correctness\n"
    << "proof are treated as an external dependency of this minimal project.\n"
    << "-/\n\n"
    << "namespace TwinPrimeExternal.GeneratedCertificate\n\n"
    << "def firstOverflowPrime : Nat := " << root << "\n"
    << "def firstOverflowSpan : Nat := " << span << "\n"
    << "def firstOverflowSplitPrimes : Nat := " << splitRoots << "\n"
    << "def firstOverflowRoutedStarts : Nat := " << routedStarts << "\n"
    << "def E_a : Nat := " << realCount << "\n"
    << "def E_p : Nat := " << predictedCount << "\n"
    << "def falsePredictedEventCount : Nat := " << falsePredicted << "\n\n"
    << "theorem E_a_eq_cap :\n"
    << "    E_a = TwinPrimeExternal.generatedMPPMCard := by\n"
    << "  norm_num [E_a, TwinPrimeExternal.generatedMPPMCard]\n\n"
    << "theorem E_p_eq_core :\n"
    << "    E_p =\n"
    << "      TwinPrimeExternal.predictedEventCount := by\n"
    << "  norm_num [E_p,\n"
    << "    TwinPrimeExternal.predictedEventCount]\n\n"
    << "theorem E_p_exceeds_E_a :\n"
    << "    E_a < E_p := by\n"
    << "  norm_num [E_a, E_p]\n\n"
    << "theorem core_predictedEventCount_exceeds_generatedMPPMCard :\n"
    << "    TwinPrimeExternal.generatedMPPMCard <\n"
    << "      TwinPrimeExternal.predictedEventCount := by\n"
    << "  simpa [E_a_eq_cap, E_p_eq_core] using E_p_exceeds_E_a\n\n"
    << "/-- Trusted external C++ certificate theorem. -/\n"
    << "axiom external_no_cofinalExceptionTail :\n"
    << "    Not (exists B,\n"
    << "      TwinPrimeExternal.CofinalExceptionTail\n"
    << "        TwinPrimeExternal.MidpointExceptionalPrime B)\n\n"
    << "end TwinPrimeExternal.GeneratedCertificate\n";
}

static void write_json_certificate(
    const string& path,
    u64 root,
    u64 span,
    u64 predictedCount,
    u64 realCount,
    u64 falsePredicted,
    u64 routedStarts,
    u64 splitRoots) {
  ofstream out(path);
  if (!out) throw runtime_error("cannot open --json-out " + path);
  out
    << "{\n"
    << "  \"firstOverflowRoot\": " << root << ",\n"
    << "  \"firstOverflowSpan\": " << span << ",\n"
    << "  \"firstOverflowSplitRoots\": " << splitRoots << ",\n"
    << "  \"firstOverflowRoutedStarts\": " << routedStarts << ",\n"
    << "  \"predictedEventCount\": " << predictedCount << ",\n"
    << "  \"generatedActualEventCount\": " << realCount << ",\n"
    << "  \"falsePredictedEventCount\": " << falsePredicted << ",\n"
    << "  \"predictedExceedsActual\": "
    << (predictedCount > realCount ? "true" : "false") << "\n"
    << "}\n";
}

int main(int argc, char** argv) {
  try {
    string certPath = "certificates/generated_mppm_pressure_certificate.json";
    u64 rstart = 191265;
    u64 maxSpan = 10000000;
    u64 capOverride = 0;
    u64 printEvery = 100;
    u64 minChild = 31;
    bool noStop = false;
    string dumpFirstPath;
    string leanOutPath;
    string jsonOutPath;

    for (int i = 1; i < argc; ++i) {
      string a = argv[i];
      auto need = [&]() -> string {
        if (++i >= argc) throw runtime_error("missing value after " + a);
        return argv[i];
      };
      if (a == "--cert") certPath = need();
      else if (a == "--rstart") rstart = stoull(need());
      else if (a == "--max-span") maxSpan = stoull(need());
      else if (a == "--cap") capOverride = stoull(need());
      else if (a == "--print-every") printEvery = stoull(need());
      else if (a == "--min-child") minChild = stoull(need());
      else if (a == "--no-stop") noStop = true;
      else if (a == "--dump-first") dumpFirstPath = need();
      else if (a == "--lean-out") leanOutPath = need();
      else if (a == "--json-out") jsonOutPath = need();
      else if (a == "--help" || a == "-h") {
        usage(argv[0]);
        return 0;
      } else {
        throw runtime_error("unknown argument " + a);
      }
    }
    if (printEvery == 0) throw runtime_error("--print-every must be positive");

    Search search;
    search.cert = load_cert(certPath);
    search.minChild = minChild;
    const u64 cap = capOverride ? capOverride : search.cert.actualCap;
    cerr << "loaded X=" << search.cert.X
         << " generatedSideLabeledMPPM=" << search.cert.actualCap
         << " predictedSideLabeledBaseUniverse=" << search.cert.predictedUniverse
         << " threshold=" << cap << "\n";

    vector<unsigned char> covered(search.cert.predictedUniverse, 0);
    u64 distinctPredictedEvents = 0;
    u64 distinctRealPredictedEvents = 0;
    u64 distinctFalsePredictedEvents = 0;
    u64 primeRoots = 0, splitRoots = 0, routedStarts = 0;
    u64 maxReachableForStart = 0;
    u64 minReachableForRouted = numeric_limits<u64>::max();
    u64 routedRootsOverActualCap = 0;
    u64 routedRootsAtOrUnderActualCap = 0;
    vector<pair<u64,u64>> smallRoutedSamples;
    unsigned long long totalReachableForRouted = 0;
    auto t0 = chrono::steady_clock::now();

    auto print_status = [&](u64 R, bool finalLine) {
      auto now = chrono::steady_clock::now();
      auto ms = chrono::duration_cast<chrono::milliseconds>(now - t0).count();
      cout << "{"
           << "\"R\":" << R
           << ",\"span\":" << (R >= rstart ? R - rstart + 1 : 0)
           << ",\"primeRoots\":" << primeRoots
           << ",\"splitRoots\":" << splitRoots
           << ",\"routedStarts\":" << routedStarts
           << ",\"distinctPredictedEvents\":" << distinctPredictedEvents
           << ",\"distinctRealPredictedEvents\":" << distinctRealPredictedEvents
           << ",\"distinctFalsePredictedEvents\":" << distinctFalsePredictedEvents
           << ",\"generatedActualCap\":" << search.cert.actualCap
           << ",\"predictedUniverse\":" << search.cert.predictedUniverse
           << ",\"cap\":" << cap
           << ",\"routedStartsExceedsCap\":" << (routedStarts > cap ? "true" : "false")
           << ",\"predictedEventsExceedActualCap\":" << (distinctPredictedEvents > search.cert.actualCap ? "true" : "false")
           << ",\"hasFalsePredictedEvent\":" << (distinctFalsePredictedEvents > 0 ? "true" : "false")
           << ",\"avgReachablePerRouted\":" << fixed << setprecision(3)
           << (routedStarts ? (double)totalReachableForRouted / routedStarts : 0.0)
           << ",\"maxReachableForStart\":" << maxReachableForStart
           << ",\"minReachableForRouted\":" << (routedStarts ? minReachableForRouted : 0)
           << ",\"routedRootsOverActualCap\":" << routedRootsOverActualCap
           << ",\"routedRootsAtOrUnderActualCap\":" << routedRootsAtOrUnderActualCap
           << ",\"targetCache\":" << search.target_cache.size()
           << ",\"childCache\":" << search.child_cache.size()
           << ",\"reachCache\":" << search.reach_cache.size()
           << ",\"productiveSlotRate\":" << fixed << setprecision(6)
           << (search.childSlotsSeen ? (double)search.productiveSlots / search.childSlotsSeen : 0.0)
           << ",\"primeAmongProductiveRate\":" << fixed << setprecision(6)
           << (search.productiveSlots ? (double)search.primeProductiveSlots / search.productiveSlots : 0.0)
           << ",\"elapsedMs\":" << ms
           << ",\"final\":" << (finalLine ? "true" : "false")
           << "}\n";
    };

    u64 nextPrint = printEvery;
    for (u64 R = rstart; R < rstart + maxSpan; ++R) {
      if (!is_prime(R)) continue;
      ++primeRoots;
      if (!leg5(R)) continue;
      ++splitRoots;
      auto ev = search.reachable_events(R);
      if (!ev.empty()) {
        if (!dumpFirstPath.empty()) {
          ofstream out(dumpFirstPath);
          if (!out) throw runtime_error("cannot open --dump-first output");
          for (int id : ev) {
            u64 code = search.cert.predictedCodes[(size_t)id];
            out << id << "," << code << ","
                << (search.cert.actualEvents.count(code) ? 1 : 0) << "\n";
          }
          dumpFirstPath.clear();
        }
        ++routedStarts;
        totalReachableForRouted += ev.size();
        maxReachableForStart = max<u64>(maxReachableForStart, ev.size());
        minReachableForRouted = min<u64>(minReachableForRouted, ev.size());
        if (ev.size() > search.cert.actualCap) ++routedRootsOverActualCap;
        else {
          ++routedRootsAtOrUnderActualCap;
          if (smallRoutedSamples.size() < 10) {
            smallRoutedSamples.push_back({R, (u64)ev.size()});
          }
        }
        for (int id : ev) {
          if (!covered[(size_t)id]) {
            covered[(size_t)id] = 1;
            ++distinctPredictedEvents;
            u64 code = search.cert.predictedCodes[(size_t)id];
            if (search.cert.actualEvents.count(code)) ++distinctRealPredictedEvents;
            else ++distinctFalsePredictedEvents;
          }
        }
      }
      if (splitRoots >= nextPrint) {
        print_status(R, false);
        while (nextPrint <= splitRoots) nextPrint += printEvery;
      }
      if (!noStop && distinctPredictedEvents > search.cert.actualCap) {
        if (!leanOutPath.empty()) {
          write_lean_certificate(
            leanOutPath, R, R - rstart + 1, distinctPredictedEvents,
            search.cert.actualCap, distinctFalsePredictedEvents,
            routedStarts, splitRoots);
        }
        if (!jsonOutPath.empty()) {
          write_json_certificate(
            jsonOutPath, R, R - rstart + 1, distinctPredictedEvents,
            search.cert.actualCap, distinctFalsePredictedEvents,
            routedStarts, splitRoots);
        }
        print_status(R, true);
        return 0;
      }
    }
    print_status(rstart + maxSpan - 1, true);
    return routedStarts > cap ? 0 : 1;
  } catch (const exception& ex) {
    cerr << "error: " << ex.what() << "\n\n";
    usage(argv[0]);
    return 2;
  }
}
