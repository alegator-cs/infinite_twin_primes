#include <algorithm>
#include <array>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using u64 = unsigned long long;
using u128 = __uint128_t;

namespace {

u64 mod_mul(u64 a, u64 b, u64 m) { return (u128)a * b % m; }
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
  static const u64 small[] = {2,3,5,7,11,13,17,19,23,29,31,37};
  for (u64 p : small) if (n % p == 0) return n == p;
  u64 d = n - 1, s = 0;
  while ((d & 1) == 0) { d >>= 1; ++s; }
  static const u64 bases[] = {2ULL,325ULL,9375ULL,28178ULL,450775ULL,9780504ULL,1795265022ULL};
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

std::mt19937_64 rng(1);
u64 pollard(u64 n) {
  if (n % 2 == 0) return 2;
  if (n % 3 == 0) return 3;
  while (true) {
    u64 c = std::uniform_int_distribution<u64>(1, n - 1)(rng);
    u64 x = std::uniform_int_distribution<u64>(0, n - 1)(rng), y = x, d = 1;
    auto f = [&](u64 v) { return (mod_mul(v, v, n) + c) % n; };
    for (int iter = 0; iter < 8000; ++iter) {
      x = f(x); y = f(f(y));
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
  if (n <= 1) {}
  else if (is_prime(n)) out.push_back(n);
  else {
    u64 d = pollard(n);
    auto a = factor_rec(d), b = factor_rec(n / d);
    out.insert(out.end(), a.begin(), a.end());
    out.insert(out.end(), b.begin(), b.end());
    std::sort(out.begin(), out.end());
  }
  factor_cache.emplace(n, out);
  return out;
}

bool leg5(u64 p) { return p > 5 && mod_pow(5 % p, (p - 1) / 2, p) == 1; }
std::vector<u64> sqrt5_mod_prime(u64 p) {
  if (!leg5(p)) return {};
  if (p % 4 == 3) {
    u64 r = mod_pow(5, (p + 1) / 4, p);
    std::vector<u64> v = {r, (p - r) % p};
    std::sort(v.begin(), v.end()); v.erase(std::unique(v.begin(), v.end()), v.end());
    return v;
  }
  u64 q = p - 1, s = 0;
  while ((q & 1) == 0) { q >>= 1; ++s; }
  u64 z = 2;
  while (mod_pow(z, (p - 1) / 2, p) != p - 1) ++z;
  u64 m = s, c = mod_pow(z, q, p), t = mod_pow(5, q, p), r = mod_pow(5, (q + 1) / 2, p);
  while (t != 1) {
    u64 i = 1, tt = mod_mul(t, t, p);
    while (tt != 1) { tt = mod_mul(tt, tt, p); ++i; }
    u64 b = mod_pow(c, 1ULL << (m - i - 1), p);
    m = i; c = mod_mul(b, b, p); t = mod_mul(t, c, p); r = mod_mul(r, b, p);
  }
  std::vector<u64> v = {r, (p - r) % p};
  std::sort(v.begin(), v.end()); v.erase(std::unique(v.begin(), v.end()), v.end());
  return v;
}

struct Row { int typ = 0; u64 u = 0; u64 h = 0; std::array<u64,5> vals{}; };
std::unordered_map<u64, std::vector<Row>> rows_cache;
std::vector<Row> rows_for(u64 p) {
  auto it = rows_cache.find(p); if (it != rows_cache.end()) return it->second;
  std::vector<Row> out;
  if (!leg5(p)) { rows_cache.emplace(p, out); return out; }
  u64 inv2 = (p + 1) / 2;
  for (u64 s : sqrt5_mod_prime(p)) {
    for (auto [typ, c] : std::vector<std::pair<int,u64>>{{1,5},{0,3}}) {
      u64 u = ((p + s + p - (c % p)) % p);
      u = mod_mul(u, inv2, p);
      u128 mid = (typ == 1) ? ((u128)(u + 1) * (u + 4) + 1) : ((u128)u * (u + 3) + 1);
      if (mid % p != 0) continue;
      u64 h = (u64)(mid / p);
      if (1 <= h && h < p) out.push_back(Row{typ, u, h, {u,u+1,u+2,u+3,u+4}});
    }
  }
  rows_cache.emplace(p, out); return out;
}

std::size_t find_matching_bracket(const std::string& s, std::size_t open) {
  int depth = 0;
  for (std::size_t i = open; i < s.size(); ++i) {
    if (s[i] == '[') ++depth;
    if (s[i] == ']') { --depth; if (depth == 0) return i; }
  }
  throw std::runtime_error("unmatched JSON array");
}
std::vector<u64> parse_array(const std::string& s, const std::string& key) {
  std::size_t pos = s.find("\"" + key + "\"");
  if (pos == std::string::npos) throw std::runtime_error("missing key " + key);
  std::size_t open = s.find('[', pos), close = find_matching_bracket(s, open);
  std::vector<u64> out; u64 val = 0; bool in = false;
  for (std::size_t i = open + 1; i < close; ++i) {
    char ch = s[i];
    if ('0' <= ch && ch <= '9') { val = val * 10 + (ch - '0'); in = true; }
    else if (in) { out.push_back(val); val = 0; in = false; }
  }
  if (in) out.push_back(val);
  return out;
}
u64 parse_scalar(const std::string& s, const std::string& key) {
  std::size_t pos = s.find("\"" + key + "\"");
  if (pos == std::string::npos) throw std::runtime_error("missing key " + key);
  pos = s.find(':', pos);
  while (pos < s.size() && !std::isdigit((unsigned char)s[pos])) ++pos;
  u64 val = 0; while (pos < s.size() && std::isdigit((unsigned char)s[pos])) { val = val * 10 + (s[pos] - '0'); ++pos; }
  return val;
}
std::vector<u64> parse_csv_u64(const std::string& s) {
  std::vector<u64> out;
  std::stringstream ss(s);
  std::string item;
  while (std::getline(ss, item, ',')) {
    if (!item.empty()) out.push_back(std::stoull(item));
  }
  return out;
}
u64 encode_event(u64 u, int side) { return (u << 1) | (u64)side; }

struct CertData {
  u64 X = 0;
  std::unordered_set<u64> actualEvents;
  std::unordered_map<u64,int> predictedEventId;
  std::vector<u64> predictedCodes;
};
CertData load_cert(const std::string& path) {
  std::ifstream in(path); if (!in) throw std::runtime_error("cannot open cert");
  std::string s((std::istreambuf_iterator<char>(in)), {});
  CertData c; c.X = parse_scalar(s, "X");
  auto basev = parse_array(s, "base"), mpv = parse_array(s, "mp"), pmv = parse_array(s, "pm");
  for (u64 u : basev) for (int side=0; side<2; ++side) {
    u64 code = encode_event(u, side);
    if (!c.predictedEventId.count(code)) { c.predictedEventId.emplace(code, (int)c.predictedEventId.size()); c.predictedCodes.push_back(code); }
  }
  for (u64 u : mpv) c.actualEvents.insert(encode_event(u,0));
  for (u64 u : pmv) c.actualEvents.insert(encode_event(u,1));
  return c;
}

struct EdgeDetail {
  u64 parent = 0, child = 0, typ = 0, u = 0, h = 0, slot = 0, quotient = 0;
};

struct Search {
  CertData cert; u64 minChild = 31; u64 saturate = 1000000000ULL;
  std::unordered_map<u64,std::vector<int>> target_unique_cache;
  std::unordered_map<u64,std::unordered_map<int,u64>> target_raw_cache;
  std::unordered_map<u64,std::vector<u64>> child_cache;
  std::unordered_map<u64,std::vector<int>> reach_unique_cache;
  std::unordered_map<u64,std::unordered_map<int,u64>> reach_raw_cache;
  std::unordered_map<u64,bool> reaches_window_cache;
  std::unordered_map<u64,u64> min_reached_parent_cache;
  std::unordered_map<u64,std::unordered_set<u64>> ancestors_cache;

  void add(std::unordered_map<int,u64>& m, int id, u64 c=1) {
    u64& x = m[id];
    if (saturate - x < c) x = saturate; else x += c;
  }
  std::unordered_map<int,u64> target_raw_at(u64 p) {
    auto it = target_raw_cache.find(p); if (it != target_raw_cache.end()) return it->second;
    std::unordered_map<int,u64> ev;
    for (const Row& r : rows_for(p)) {
      if (p < cert.X) {
        for (u64 targetU = r.u; targetU < cert.X; targetU += p) {
          for (int side=0; side<2; ++side) {
            auto im = cert.predictedEventId.find(encode_event(targetU, side));
            if (im != cert.predictedEventId.end()) add(ev, im->second);
          }
        }
      } else if (r.u < cert.X) {
        for (int side=0; side<2; ++side) {
          auto im = cert.predictedEventId.find(encode_event(r.u, side));
          if (im != cert.predictedEventId.end()) add(ev, im->second);
        }
      }
    }
    target_raw_cache.emplace(p, ev); return ev;
  }
  std::vector<int> target_unique_at(u64 p) {
    auto raw = target_raw_at(p); std::vector<int> out; out.reserve(raw.size());
    for (auto& kv : raw) out.push_back(kv.first);
    std::sort(out.begin(), out.end()); return out;
  }
  std::vector<u64> child_edges(u64 p) {
    auto it = child_cache.find(p); if (it != child_cache.end()) return it->second;
    std::vector<u64> out;
    for (const Row& r : rows_for(p)) for (u64 v : r.vals) {
      auto fs = factor_rec(v);
      for (u64 q : fs) if (minChild <= q && q < p && leg5(q)) out.push_back(q);
    }
    std::sort(out.begin(), out.end(), std::greater<u64>()); out.erase(std::unique(out.begin(), out.end()), out.end());
    child_cache.emplace(p, out); return out;
  }

  EdgeDetail edge_detail(u64 p, u64 child) {
    for (const Row& r : rows_for(p)) {
      for (u64 slot = 0; slot < r.vals.size(); ++slot) {
        u64 v = r.vals[(std::size_t)slot];
        if (v % child == 0) {
          auto fs = factor_rec(v);
          if (std::find(fs.begin(), fs.end(), child) != fs.end() &&
              minChild <= child && child < p && leg5(child)) {
            return EdgeDetail{p, child, (u64)r.typ, r.u, r.h, slot, v / child};
          }
        }
      }
    }
    throw std::runtime_error("missing edge detail");
  }

  std::vector<int> reach_unique(u64 p) {
    auto it = reach_unique_cache.find(p); if (it != reach_unique_cache.end()) return it->second;
    std::vector<int> ev = target_unique_at(p);
    for (u64 q : child_edges(p)) { auto child = reach_unique(q); ev.insert(ev.end(), child.begin(), child.end()); }
    std::sort(ev.begin(), ev.end()); ev.erase(std::unique(ev.begin(), ev.end()), ev.end());
    reach_unique_cache.emplace(p, ev); return ev;
  }
  std::unordered_map<int,u64> reach_raw(u64 p) {
    auto it = reach_raw_cache.find(p); if (it != reach_raw_cache.end()) return it->second;
    std::unordered_map<int,u64> ev = target_raw_at(p);
    for (u64 q : child_edges(p)) {
      auto child = reach_raw(q);
      for (auto& kv : child) add(ev, kv.first, kv.second);
    }
    reach_raw_cache.emplace(p, ev); return ev;
  }

  bool reaches_window(u64 p) {
    auto it = reaches_window_cache.find(p);
    if (it != reaches_window_cache.end()) return it->second;
    bool ok = p < cert.X || !target_unique_at(p).empty();
    if (!ok) {
      for (u64 q : child_edges(p)) {
        if (reaches_window(q)) { ok = true; break; }
      }
    }
    reaches_window_cache.emplace(p, ok);
    return ok;
  }

  u64 min_reached_parent(u64 p) {
    auto it = min_reached_parent_cache.find(p);
    if (it != min_reached_parent_cache.end()) return it->second;
    u64 best = p;
    for (u64 q : child_edges(p)) best = std::min(best, min_reached_parent(q));
    min_reached_parent_cache.emplace(p, best);
    return best;
  }

  std::unordered_set<u64> ancestors(u64 p) {
    auto it = ancestors_cache.find(p);
    if (it != ancestors_cache.end()) return it->second;
    std::unordered_set<u64> out;
    out.insert(p);
    for (u64 q : child_edges(p)) {
      auto child = ancestors(q);
      out.insert(child.begin(), child.end());
    }
    ancestors_cache.emplace(p, out);
    return out;
  }

  bool path_to_child(u64 p, u64 target, std::vector<EdgeDetail>& path) {
    if (p == target) return true;
    for (u64 q : child_edges(p)) {
      if (q == target) {
        path.push_back(edge_detail(p, q));
        return true;
      }
      if (q > target && ancestors(q).count(target)) {
        path.push_back(edge_detail(p, q));
        if (path_to_child(q, target, path)) return true;
        path.pop_back();
      }
    }
    return false;
  }
};

struct Stats { u64 starts=0, directRaw=0, directUnique=0, recursiveRaw=0, recursiveUnique=0, actualUnique=0, maxFiber=0, fiberGt2=0; };

void merge_raw(std::unordered_map<int,u64>& dst, const std::unordered_map<int,u64>& src, u64 sat) {
  for (auto& kv : src) {
    u64& x = dst[kv.first];
    if (sat - x < kv.second) x = sat; else x += kv.second;
  }
}

} // namespace

int main(int argc, char** argv) {
  std::string certPath = "certificates/generated_mppm_pressure_certificate.json";
  u64 start = 191281, end = 191281;
  bool recursive = true;
  u64 perSeed = 0;
  u64 scanSeeds = 0;
  u64 childFreqSeeds = 0;
  u64 strongChildSeeds = 0;
  u64 coverSeeds = 0;
  u64 coverChildMax = 0;
  u64 windowSeeds = 0;
  u64 windowUnionSeeds = 0;
  std::vector<u64> windowUnionWidths;
  u64 recoverySeeds = 0;
  std::vector<u64> recoveryPrefixes;
  u64 recoveryMaxExtra = 200;
  u64 recoverOnePrefix = 0;
  u64 recoverOneIndex = 1;
  u64 recoverOneMaxExtra = 1000;
  u64 recoverOneReportEvery = 100;
  u64 cumulativeSeeds = 0;
  u64 cumulativeEvery = 25;
  u64 descentSeeds = 0;
  u64 ascentSeeds = 0;
  u64 ascentChild = 0;
  u64 ascentMod = 0;
  u64 ascentDetails = 0;
  u64 eventFreqSeeds = 0;
  u64 eventFreqTop = 30;
  bool eventFalseOnly = false;
  u64 pathSeeds = 0;
  u64 pathChild = 31;
  u64 badChildSeeds = 0;
  u64 badChild = 31;
  u64 bottomSeeds = 0;
  bool bottomFast = false;
  u64 cutoffSeeds = 0;
  std::vector<u64> cutoffs = {31, 41, 127, 1000, 10000, 250000, 30000000};
  u64 growthParent = 0;
  std::vector<u64> growthWindows;
  for (int i=1; i<argc; ++i) {
    std::string a=argv[i]; auto need=[&](){ if (++i>=argc) throw std::runtime_error("missing arg"); return std::string(argv[i]); };
    if (a=="--cert") certPath=need();
    else if (a=="--start") start=std::stoull(need());
    else if (a=="--end") end=std::stoull(need());
    else if (a=="--direct-only") recursive=false;
    else if (a=="--per-seed") perSeed=std::stoull(need());
    else if (a=="--scan-seeds") scanSeeds=std::stoull(need());
    else if (a=="--child-frequency") childFreqSeeds=std::stoull(need());
    else if (a=="--strong-child") strongChildSeeds=std::stoull(need());
    else if (a=="--cover-seeds") coverSeeds=std::stoull(need());
    else if (a=="--cover-child-max") coverChildMax=std::stoull(need());
    else if (a=="--window-seeds") windowSeeds=std::stoull(need());
    else if (a=="--window-union") windowUnionSeeds=std::stoull(need());
    else if (a=="--window-union-widths") windowUnionWidths=parse_csv_u64(need());
    else if (a=="--recovery-seeds") recoverySeeds=std::stoull(need());
    else if (a=="--recovery-prefixes") recoveryPrefixes=parse_csv_u64(need());
    else if (a=="--recovery-max-extra") recoveryMaxExtra=std::stoull(need());
    else if (a=="--recover-one-prefix") recoverOnePrefix=std::stoull(need());
    else if (a=="--recover-one-index") recoverOneIndex=std::stoull(need());
    else if (a=="--recover-one-max-extra") recoverOneMaxExtra=std::stoull(need());
    else if (a=="--recover-one-report-every") recoverOneReportEvery=std::stoull(need());
    else if (a=="--cumulative-seeds") cumulativeSeeds=std::stoull(need());
    else if (a=="--cumulative-every") cumulativeEvery=std::stoull(need());
    else if (a=="--descent-seeds") descentSeeds=std::stoull(need());
    else if (a=="--ascent-seeds") ascentSeeds=std::stoull(need());
    else if (a=="--ascent-child") ascentChild=std::stoull(need());
    else if (a=="--ascent-mod") ascentMod=std::stoull(need());
    else if (a=="--ascent-details") ascentDetails=std::stoull(need());
    else if (a=="--event-frequency") eventFreqSeeds=std::stoull(need());
    else if (a=="--event-top") eventFreqTop=std::stoull(need());
    else if (a=="--event-false-only") eventFalseOnly=true;
    else if (a=="--path-seeds") pathSeeds=std::stoull(need());
    else if (a=="--path-child") pathChild=std::stoull(need());
    else if (a=="--bad-child-seeds") badChildSeeds=std::stoull(need());
    else if (a=="--bad-child") badChild=std::stoull(need());
    else if (a=="--bottom-frequency") bottomSeeds=std::stoull(need());
    else if (a=="--bottom-fast") bottomFast=true;
    else if (a=="--cutoff-seeds") cutoffSeeds=std::stoull(need());
    else if (a=="--cutoffs") cutoffs=parse_csv_u64(need());
    else if (a=="--growth-parent") growthParent=std::stoull(need());
    else if (a=="--growth-windows") growthWindows=parse_csv_u64(need());
    else throw std::runtime_error("unknown arg " + a);
  }
  Search s; s.cert = load_cert(certPath);

  if (growthParent != 0) {
    std::sort(growthWindows.begin(), growthWindows.end());
    growthWindows.erase(std::unique(growthWindows.begin(), growthWindows.end()), growthWindows.end());
    if (growthWindows.empty()) growthWindows = {512,1000,10000,100000,250000,1000000,30000000};
    CertData baseCert = s.cert;
    std::cout << "growth parent=" << growthParent << "\n";
    for (u64 X : growthWindows) {
      Search gx;
      gx.cert = baseCert;
      gx.cert.X = X;
      auto pred = gx.reach_unique(growthParent);
      u64 actualCap = 0, actualInPred = 0;
      std::unordered_set<int> predSet(pred.begin(), pred.end());
      for (u64 code : baseCert.actualEvents) {
        if ((code >> 1) < X) ++actualCap;
      }
      for (int id : pred) {
        if (id >= 0 && (std::size_t)id < baseCert.predictedCodes.size()) {
          u64 code = baseCert.predictedCodes[(std::size_t)id];
          if (baseCert.actualEvents.count(code)) ++actualInPred;
        }
      }
      std::cout << "X=" << X
                << " predicted=" << pred.size()
                << " actualCap=" << actualCap
                << " actualInPred=" << actualInPred
                << " falseInPred=" << (pred.size() - actualInPred)
                << "\n";
    }
    return 0;
  }

  if (cumulativeSeeds != 0) {
    if (cumulativeEvery == 0) cumulativeEvery = 1;
    std::unordered_set<int> cumulative;
    u64 seenSeeds = 0, prev = 0;
    std::cout << "cumulative start>=" << start
              << " seeds=" << cumulativeSeeds
              << " every=" << cumulativeEvery
              << " cap=95568 predictedUniverse=" << s.cert.predictedCodes.size()
              << "\n";
    for (u64 p = start; seenSeeds < cumulativeSeeds; ++p) {
      if (!is_prime(p) || !leg5(p)) continue;
      ++seenSeeds;
      auto rec = s.reach_unique(p);
      u64 fresh = 0, actual = 0;
      for (int id : rec) {
        u64 code = s.cert.predictedCodes[(std::size_t)id];
        if (s.cert.actualEvents.count(code)) ++actual;
        if (!cumulative.count(id)) ++fresh;
      }
      for (int id : rec) cumulative.insert(id);
      if (seenSeeds == 1 || seenSeeds == cumulativeSeeds ||
          seenSeeds % cumulativeEvery == 0 || fresh == 0) {
        std::cout << "seed#" << seenSeeds
                  << " p=" << p
                  << " gap=" << (prev == 0 ? 0 : p - prev)
                  << " recursiveUnique=" << rec.size()
                  << " actualUnique=" << actual
                  << " freshVsPrior=" << fresh
                  << " cumulativeUnique=" << cumulative.size()
                  << "\n";
      }
      prev = p;
    }
    return 0;
  }

  if (cutoffSeeds != 0) {
    std::sort(cutoffs.begin(), cutoffs.end());
    cutoffs.erase(std::unique(cutoffs.begin(), cutoffs.end()), cutoffs.end());
    std::vector<u64> hit(cutoffs.size(), 0);
    u64 seenSeeds = 0, noChild = 0, maxBottom = 0, maxBottomSeed = 0;
    std::unordered_map<u64,u64> bottomFreq;
    for (u64 p = start; seenSeeds < cutoffSeeds; ++p) {
      if (!is_prime(p) || !leg5(p)) continue;
      ++seenSeeds;
      if (s.child_edges(p).empty()) ++noChild;
      u64 b = s.min_reached_parent(p);
      ++bottomFreq[b];
      if (b > maxBottom) { maxBottom = b; maxBottomSeed = p; }
      for (std::size_t i = 0; i < cutoffs.size(); ++i) {
        if (b <= cutoffs[i]) ++hit[i];
      }
    }
    std::cout << "cutoff-reach start>=" << start
              << " seeds=" << seenSeeds
              << " noChild=" << noChild
              << " maxBottom=" << maxBottom
              << " atSeed=" << maxBottomSeed
              << "\n";
    for (std::size_t i = 0; i < cutoffs.size(); ++i) {
      std::cout << "cutoff<=" << cutoffs[i]
                << " hit=" << hit[i]
                << " miss=" << (seenSeeds - hit[i])
                << "\n";
    }
    std::vector<std::pair<u64,u64>> bottoms(bottomFreq.begin(), bottomFreq.end());
    std::sort(bottoms.begin(), bottoms.end(), [](auto a, auto b) {
      if (a.second != b.second) return a.second > b.second;
      return a.first < b.first;
    });
    for (std::size_t i = 0; i < std::min<std::size_t>(20, bottoms.size()); ++i) {
      std::cout << "bottom=" << bottoms[i].first
                << " count=" << bottoms[i].second
                << "\n";
    }
    return 0;
  }

  if (bottomSeeds != 0) {
    u64 seenSeeds = 0;
    std::unordered_map<u64,u64> freq;
    std::unordered_map<u64,u64> reachSizeMin;
    for (u64 p = start; seenSeeds < bottomSeeds; ++p) {
      if (!is_prime(p) || !leg5(p)) continue;
      ++seenSeeds;
      u64 b = s.min_reached_parent(p);
      ++freq[b];
      if (!bottomFast) {
        u64 r = (u64)s.reach_unique(p).size();
        auto it = reachSizeMin.find(b);
        if (it == reachSizeMin.end() || r < it->second) reachSizeMin[b] = r;
      }
    }
    std::vector<std::pair<u64,u64>> items(freq.begin(), freq.end());
    std::sort(items.begin(), items.end(), [](auto a, auto b) {
      if (a.second != b.second) return a.second > b.second;
      return a.first < b.first;
    });
    std::cout << "bottom-frequency start>=" << start
              << " seeds=" << seenSeeds
              << " distinctBottoms=" << items.size()
              << "\n";
    for (std::size_t i = 0; i < std::min<std::size_t>(50, items.size()); ++i) {
      auto [b, count] = items[i];
      std::cout << "bottom=" << b
                << " count=" << count;
      if (!bottomFast) std::cout << " minReach=" << reachSizeMin[b];
      std::cout << "\n";
    }
    return 0;
  }

  if (badChildSeeds != 0) {
    u64 seenSeeds = 0, bad = 0, noChild = 0, maxMinParent = 0, maxMinSeed = 0;
    std::cout << "bad-child start>=" << start
              << " seeds=" << badChildSeeds
              << " target=" << badChild
              << "\n";
    for (u64 p = start; seenSeeds < badChildSeeds; ++p) {
      if (!is_prime(p) || !leg5(p)) continue;
      ++seenSeeds;
      auto children = s.child_edges(p);
      if (children.empty()) ++noChild;
      auto an = s.ancestors(p);
      bool ok = an.count(badChild) != 0;
      u64 minParent = s.min_reached_parent(p);
      if (minParent > maxMinParent) { maxMinParent = minParent; maxMinSeed = p; }
      if (!ok) {
        ++bad;
        if (bad <= 50) {
          std::cout << "bad#" << bad
                    << " seed#" << seenSeeds
                    << " p=" << p
                    << " childCount=" << children.size()
                    << " minReachedParent=" << minParent
                    << " recursiveUnique=" << s.reach_unique(p).size()
                    << "\n";
        }
      }
    }
    std::cout << "summary bad=" << bad
              << " good=" << (seenSeeds - bad)
              << " noChild=" << noChild
              << " maxMinReachedParent=" << maxMinParent
              << " atSeed=" << maxMinSeed
              << "\n";
    return 0;
  }

  if (pathSeeds != 0) {
    u64 seenSeeds = 0, hit = 0, maxDepth = 0;
    std::unordered_map<u64,u64> depthFreq;
    std::cout << "paths start>=" << start
              << " seeds=" << pathSeeds
              << " target=" << pathChild
              << "\n";
    for (u64 p = start; seenSeeds < pathSeeds; ++p) {
      if (!is_prime(p) || !leg5(p)) continue;
      ++seenSeeds;
      std::vector<EdgeDetail> path;
      bool ok = s.path_to_child(p, pathChild, path);
      if (ok) {
        ++hit;
        ++depthFreq[(u64)path.size()];
        maxDepth = std::max<u64>(maxDepth, (u64)path.size());
      }
      if (seenSeeds <= 40 || !ok) {
        std::cout << "seed#" << seenSeeds
                  << " p=" << p
                  << " hit=" << (ok ? 1 : 0)
                  << " depth=" << path.size()
                  << " path=";
        if (path.empty()) {
          std::cout << p;
        } else {
          std::cout << path.front().parent;
          for (auto const& e : path) std::cout << "->" << e.child;
        }
        std::cout << "\n";
        for (auto const& e : path) {
          std::cout << "  edge parent=" << e.parent
                    << " child=" << e.child
                    << " typ=" << e.typ
                    << " u=" << e.u
                    << " h=" << e.h
                    << " slot=" << e.slot
                    << " quotient=" << e.quotient
                    << "\n";
        }
      }
    }
    std::vector<std::pair<u64,u64>> items(depthFreq.begin(), depthFreq.end());
    std::sort(items.begin(), items.end());
    std::cout << "summary hit=" << hit
              << " miss=" << (seenSeeds - hit)
              << " maxDepth=" << maxDepth
              << "\n";
    for (auto [depth, count] : items) {
      std::cout << "depth=" << depth << " count=" << count << "\n";
    }
    return 0;
  }

  if (eventFreqSeeds != 0) {
    std::unordered_map<int,u64> freq;
    std::unordered_map<int,u64> actualFreq;
    u64 seenSeeds = 0;
    for (u64 p = start; seenSeeds < eventFreqSeeds; ++p) {
      if (!is_prime(p) || !leg5(p)) continue;
      ++seenSeeds;
      for (int id : s.reach_unique(p)) {
        u64 code = s.cert.predictedCodes[(std::size_t)id];
        bool actual = s.cert.actualEvents.count(code) != 0;
        if (eventFalseOnly && actual) continue;
        ++freq[id];
        if (actual) ++actualFreq[id];
      }
    }
    std::vector<std::pair<int,u64>> items(freq.begin(), freq.end());
    std::sort(items.begin(), items.end(), [](auto a, auto b) {
      if (a.second != b.second) return a.second > b.second;
      return a.first < b.first;
    });
    std::cout << "event-frequency start>=" << start
              << " seeds=" << seenSeeds
              << " falseOnly=" << (eventFalseOnly ? 1 : 0)
              << " distinctEvents=" << items.size()
              << "\n";
    std::size_t limit = std::min<std::size_t>((std::size_t)eventFreqTop, items.size());
    for (std::size_t i = 0; i < limit; ++i) {
      int id = items[i].first;
      u64 code = s.cert.predictedCodes[(std::size_t)id];
      std::cout << "rank=" << (i+1)
                << " eventId=" << id
                << " u=" << (code >> 1)
                << " side=" << (code & 1)
                << " freq=" << items[i].second
                << " actualFreq=" << actualFreq[id]
                << " actual=" << (s.cert.actualEvents.count(code) ? 1 : 0)
                << "\n";
    }
    return 0;
  }

  if (ascentSeeds != 0) {
    if (ascentChild == 0) throw std::runtime_error("--ascent-child is required");
    if (ascentMod == 0) ascentMod = ascentChild;
    u64 seenSeeds = 0, hits = 0;
    std::unordered_map<u64,u64> hitResidues, allResidues;
    std::cout << "ascent start>=" << start
              << " seeds=" << ascentSeeds
              << " child=" << ascentChild
              << " mod=" << ascentMod
              << "\n";
    for (u64 p = start; seenSeeds < ascentSeeds; ++p) {
      if (!is_prime(p) || !leg5(p)) continue;
      ++seenSeeds;
      ++allResidues[p % ascentMod];
      auto children = s.child_edges(p);
      bool hit = std::binary_search(children.rbegin(), children.rend(), ascentChild);
      // child_edges is stored descending; fall back to a linear check if the
      // reverse-iterator search misses due to an ordering mistake.
      if (!hit) hit = std::find(children.begin(), children.end(), ascentChild) != children.end();
      if (hit) {
        ++hits;
        ++hitResidues[p % ascentMod];
      }
      if (seenSeeds <= 30 || hit) {
        std::cout << "seed#" << seenSeeds
                  << " p=" << p
                  << " residue=" << (p % ascentMod)
                  << " hit=" << (hit ? 1 : 0)
                  << " childCount=" << children.size()
                  << "\n";
        if (hit && ascentDetails != 0 && hits <= ascentDetails) {
          auto e = s.edge_detail(p, ascentChild);
          std::cout << "  edge parent=" << e.parent
                    << " child=" << e.child
                    << " typ=" << e.typ
                    << " u=" << e.u
                    << " h=" << e.h
                    << " slot=" << e.slot
                    << " value=" << (e.child * e.quotient)
                    << " quotient=" << e.quotient
                    << "\n";
        }
      }
    }
    std::vector<std::pair<u64,u64>> items(hitResidues.begin(), hitResidues.end());
    std::sort(items.begin(), items.end(), [](auto a, auto b) {
      if (a.second != b.second) return a.second > b.second;
      return a.first < b.first;
    });
    std::cout << "summary hits=" << hits
              << " misses=" << (seenSeeds - hits)
              << " hitResidues=" << items.size()
              << "\n";
    for (std::size_t i = 0; i < std::min<std::size_t>(30, items.size()); ++i) {
      auto [res, cnt] = items[i];
      std::cout << "residue=" << res
                << " hits=" << cnt
                << " all=" << allResidues[res]
                << "\n";
    }
    return 0;
  }

  if (descentSeeds != 0) {
    u64 seenSeeds = 0, reaches = 0, noReach = 0, noChild = 0;
    u64 maxMinParent = 0, maxMinParentSeed = 0;
    u64 minReachUnique = ~0ULL, minReachUniqueSeed = 0;
    std::cout << "descent start>=" << start
              << " seeds=" << descentSeeds
              << " X=" << s.cert.X
              << "\n";
    for (u64 p = start; seenSeeds < descentSeeds; ++p) {
      if (!is_prime(p) || !leg5(p)) continue;
      ++seenSeeds;
      auto children = s.child_edges(p);
      auto ancestors = s.ancestors(p);
      if (children.empty()) ++noChild;
      bool hit = s.reaches_window(p);
      if (hit) ++reaches; else ++noReach;
      u64 minParent = s.min_reached_parent(p);
      if (minParent > maxMinParent) {
        maxMinParent = minParent;
        maxMinParentSeed = p;
      }
      auto rec = s.reach_unique(p);
      if (rec.size() < minReachUnique) {
        minReachUnique = (u64)rec.size();
        minReachUniqueSeed = p;
      }
      if (!hit || seenSeeds <= 20) {
        std::cout << "seed#" << seenSeeds
                  << " p=" << p
                  << " childCount=" << children.size()
                  << " reachesWindow=" << (hit ? 1 : 0)
                  << " minReachedParent=" << minParent
                  << " has31=" << (ancestors.count(31) ? 1 : 0)
                  << " has71=" << (ancestors.count(71) ? 1 : 0)
                  << " has811=" << (ancestors.count(811) ? 1 : 0)
                  << " recursiveUnique=" << rec.size()
                  << "\n";
      }
    }
    std::cout << "summary reachesWindow=" << reaches
              << " noReach=" << noReach
              << " noChild=" << noChild
              << " maxMinReachedParent=" << maxMinParent
              << " atSeed=" << maxMinParentSeed
              << " minRecursiveUnique=" << minReachUnique
              << " atSeed=" << minReachUniqueSeed
              << "\n";
    return 0;
  }

  if (windowSeeds != 0) {
    std::vector<u64> reaches;
    std::vector<u64> primes;
    reaches.reserve((std::size_t)windowSeeds);
    primes.reserve((std::size_t)windowSeeds);
    for (u64 p = start; reaches.size() < windowSeeds; ++p) {
      if (!is_prime(p) || !leg5(p)) continue;
      primes.push_back(p);
      reaches.push_back((u64)s.reach_unique(p).size());
    }
    std::cout << "window start>=" << start << " seeds=" << windowSeeds << "\n";
    for (u64 w : {1ULL,2ULL,3ULL,5ULL,10ULL,20ULL,50ULL,100ULL}) {
      if (w > reaches.size()) continue;
      u64 minMax = ~0ULL, minSum = ~0ULL, badMax = 0, badSum = 0, minAt = 0;
      for (std::size_t i = 0; i + w <= reaches.size(); ++i) {
        u64 mx = 0, sum = 0;
        for (std::size_t j = i; j < i + w; ++j) {
          mx = std::max(mx, reaches[j]);
          sum += reaches[j];
        }
        if (mx < minMax) { minMax = mx; minAt = (u64)i; }
        minSum = std::min(minSum, sum);
        if (mx <= 95568) ++badMax;
        if (sum <= 95568) ++badSum;
      }
      std::cout << "w=" << w
                << " minMax=" << minMax
                << " minMaxAtSeed#" << (minAt+1)
                << " p=" << primes[(std::size_t)minAt]
                << " badWindowsByMax=" << badMax
                << " minSum=" << minSum
                << " badWindowsBySum=" << badSum
                << "\n";
    }
    return 0;
  }

  if (windowUnionSeeds != 0) {
    if (windowUnionWidths.empty()) windowUnionWidths = {1,2,3,5,10,20,50,100};
    std::sort(windowUnionWidths.begin(), windowUnionWidths.end());
    windowUnionWidths.erase(std::unique(windowUnionWidths.begin(), windowUnionWidths.end()), windowUnionWidths.end());
    std::vector<std::vector<int>> reaches;
    std::vector<u64> primes;
    reaches.reserve((std::size_t)windowUnionSeeds);
    primes.reserve((std::size_t)windowUnionSeeds);
    for (u64 p = start; reaches.size() < windowUnionSeeds; ++p) {
      if (!is_prime(p) || !leg5(p)) continue;
      primes.push_back(p);
      reaches.push_back(s.reach_unique(p));
    }
    std::cout << "window-union start>=" << start
              << " seeds=" << windowUnionSeeds
              << " cap=95568 predictedUniverse=" << s.cert.predictedCodes.size()
              << "\n";
    for (u64 w : windowUnionWidths) {
      if (w == 0 || w > reaches.size()) continue;
      u64 minUnion = ~0ULL, maxUnion = 0, badUnion = 0, minAt = 0;
      u64 minActual = ~0ULL, minFalse = ~0ULL;
      for (std::size_t i = 0; i + w <= reaches.size(); ++i) {
        std::unordered_set<int> uni;
        for (std::size_t j = i; j < i + w; ++j) {
          uni.insert(reaches[j].begin(), reaches[j].end());
        }
        u64 actual = 0;
        for (int id : uni) {
          u64 code = s.cert.predictedCodes[(std::size_t)id];
          if (s.cert.actualEvents.count(code)) ++actual;
        }
        u64 falseCount = (u64)uni.size() - actual;
        if (uni.size() < minUnion) {
          minUnion = (u64)uni.size();
          minAt = (u64)i;
          minActual = actual;
          minFalse = falseCount;
        }
        maxUnion = std::max<u64>(maxUnion, (u64)uni.size());
        if (uni.size() <= 95568) ++badUnion;
      }
      std::cout << "w=" << w
                << " minUnion=" << minUnion
                << " minUnionAtSeed#" << (minAt + 1)
                << " p=" << primes[(std::size_t)minAt]
                << " minActual=" << minActual
                << " minFalse=" << minFalse
                << " maxUnion=" << maxUnion
                << " badWindowsByUnion=" << badUnion
                << "\n";
    }
    return 0;
  }

  if (recoverOnePrefix != 0) {
    if (recoverOneIndex == 0) recoverOneIndex = 1;
    if (recoverOneReportEvery == 0) recoverOneReportEvery = 1;
    std::vector<std::vector<int>> reaches;
    std::vector<u64> primes;
    u64 needInitial = recoverOneIndex + recoverOnePrefix;
    reaches.reserve((std::size_t)(needInitial + 16));
    primes.reserve((std::size_t)(needInitial + 16));
    u64 p = start;
    while (reaches.size() < needInitial) {
      if (is_prime(p) && leg5(p)) {
        primes.push_back(p);
        reaches.push_back(s.reach_unique(p));
      }
      ++p;
    }
    std::size_t i = (std::size_t)(recoverOneIndex - 1);
    std::size_t prefix = (std::size_t)recoverOnePrefix;
    auto add_range = [&](std::unordered_set<int>& out, std::size_t lo, std::size_t hi) {
      for (std::size_t j = lo; j < hi; ++j) {
        out.insert(reaches[j].begin(), reaches[j].end());
      }
    };
    std::unordered_set<int> oldUnion, shifted;
    add_range(oldUnion, i, i + prefix);
    add_range(shifted, i + 1, i + prefix);
    std::unordered_set<int> remaining;
    for (int id : oldUnion) if (!shifted.count(id)) remaining.insert(id);
    std::cout << "recover-one start>=" << start
              << " index=" << recoverOneIndex
              << " prefix=" << recoverOnePrefix
              << " firstSeed=" << primes[i]
              << " oldUnion=" << oldUnion.size()
              << " shifted=" << shifted.size()
              << " lost=" << remaining.size()
              << " maxExtra=" << recoverOneMaxExtra
              << "\n";
    std::unordered_set<int> grow = shifted;
    u64 extra = 0, lastReportedRemaining = (u64)remaining.size();
    while (!remaining.empty() && extra < recoverOneMaxExtra) {
      while (reaches.size() <= i + prefix + (std::size_t)extra) {
        if (is_prime(p) && leg5(p)) {
          primes.push_back(p);
          reaches.push_back(s.reach_unique(p));
        }
        ++p;
      }
      std::size_t idx = i + prefix + (std::size_t)extra;
      for (int id : reaches[idx]) {
        grow.insert(id);
        remaining.erase(id);
      }
      ++extra;
      if (extra == 1 || extra % recoverOneReportEvery == 0 ||
          remaining.empty() || remaining.size() < lastReportedRemaining / 2) {
        std::cout << "extra=" << extra
                  << " seed=" << primes[idx]
                  << " union=" << grow.size()
                  << " remainingLost=" << remaining.size()
                  << "\n";
        lastReportedRemaining = (u64)remaining.size();
      }
    }
    std::cout << "summary recovered=" << (remaining.empty() ? 1 : 0)
              << " extraUsed=" << extra
              << " finalUnion=" << grow.size()
              << " remainingLost=" << remaining.size()
              << "\n";
    if (!remaining.empty()) {
      std::size_t shown = 0;
      for (int id : remaining) {
        u64 code = s.cert.predictedCodes[(std::size_t)id];
        std::cout << "remaining eventId=" << id
                  << " u=" << (code >> 1)
                  << " side=" << (code & 1)
                  << " actual=" << (s.cert.actualEvents.count(code) ? 1 : 0)
                  << "\n";
        if (++shown >= 20) break;
      }
    }
    return 0;
  }

  if (recoverySeeds != 0) {
    if (recoveryPrefixes.empty()) recoveryPrefixes = {1,2,3,5,10,20,50};
    std::sort(recoveryPrefixes.begin(), recoveryPrefixes.end());
    recoveryPrefixes.erase(std::unique(recoveryPrefixes.begin(), recoveryPrefixes.end()), recoveryPrefixes.end());
    std::vector<std::vector<int>> reaches;
    std::vector<u64> primes;
    u64 needSeeds = recoverySeeds + recoveryMaxExtra + 2;
    reaches.reserve((std::size_t)needSeeds);
    primes.reserve((std::size_t)needSeeds);
    for (u64 p = start; reaches.size() < needSeeds; ++p) {
      if (!is_prime(p) || !leg5(p)) continue;
      primes.push_back(p);
      reaches.push_back(s.reach_unique(p));
    }
    auto union_range = [&](std::size_t lo, std::size_t hi) {
      std::unordered_set<int> out;
      for (std::size_t j = lo; j < hi; ++j) {
        out.insert(reaches[j].begin(), reaches[j].end());
      }
      return out;
    };
    std::cout << "recovery start>=" << start
              << " seeds=" << recoverySeeds
              << " maxExtra=" << recoveryMaxExtra
              << " cap=95568 predictedUniverse=" << s.cert.predictedCodes.size()
              << "\n";
    for (u64 prefix : recoveryPrefixes) {
      if (prefix == 0 || prefix > recoverySeeds) continue;
      u64 windows = recoverySeeds - prefix + 1;
      u64 maxExtraForOldCount = 0, maxExtraForCap = 0, maxExtraForLostEvents = 0;
      u64 failOldCount = 0, failCap = 0, failLostEvents = 0;
      u64 maxLost = 0, maxDrop = 0, minOld = ~0ULL, minShift = ~0ULL;
      u64 worstOldIndex = 0, worstCapIndex = 0, worstLostIndex = 0, worstLostRecoverIndex = 0;
      u64 sumLost = 0, sumDrop = 0, sumExtraOld = 0, sumExtraCap = 0, sumExtraLostEvents = 0;
      for (std::size_t i = 0; i < windows; ++i) {
        auto oldUnion = union_range(i, i + (std::size_t)prefix);
        auto shifted = union_range(i + 1, i + (std::size_t)prefix);
        u64 oldSize = (u64)oldUnion.size();
        u64 shiftSize = (u64)shifted.size();
        minOld = std::min(minOld, oldSize);
        minShift = std::min(minShift, shiftSize);
        std::vector<int> lostEvents;
        for (int id : oldUnion) if (!shifted.count(id)) lostEvents.push_back(id);
        u64 lost = (u64)lostEvents.size();
        u64 drop = oldSize > shiftSize ? oldSize - shiftSize : 0;
        sumLost += lost;
        sumDrop += drop;
        if (lost > maxLost) { maxLost = lost; worstLostIndex = (u64)i; }
        if (drop > maxDrop) maxDrop = drop;

        u64 extraOld = 0;
        auto growOld = shifted;
        while (growOld.size() < oldSize && extraOld < recoveryMaxExtra) {
          std::size_t idx = i + (std::size_t)prefix + (std::size_t)extraOld;
          growOld.insert(reaches[idx].begin(), reaches[idx].end());
          ++extraOld;
        }
        if (growOld.size() < oldSize) {
          ++failOldCount;
          worstOldIndex = (u64)i;
        } else {
          maxExtraForOldCount = std::max(maxExtraForOldCount, extraOld);
          sumExtraOld += extraOld;
        }

        u64 extraCap = 0;
        auto growCap = shifted;
        while (growCap.size() <= 95568 && extraCap < recoveryMaxExtra) {
          std::size_t idx = i + (std::size_t)prefix + (std::size_t)extraCap;
          growCap.insert(reaches[idx].begin(), reaches[idx].end());
          ++extraCap;
        }
        if (growCap.size() <= 95568) {
          ++failCap;
          worstCapIndex = (u64)i;
        } else {
          maxExtraForCap = std::max(maxExtraForCap, extraCap);
          sumExtraCap += extraCap;
        }

        u64 extraLostEvents = 0;
        auto growLost = shifted;
        auto lost_recovered = [&]() {
          for (int id : lostEvents) if (!growLost.count(id)) return false;
          return true;
        };
        while (!lost_recovered() && extraLostEvents < recoveryMaxExtra) {
          std::size_t idx = i + (std::size_t)prefix + (std::size_t)extraLostEvents;
          growLost.insert(reaches[idx].begin(), reaches[idx].end());
          ++extraLostEvents;
        }
        if (!lost_recovered()) {
          ++failLostEvents;
          worstLostRecoverIndex = (u64)i;
        } else {
          maxExtraForLostEvents = std::max(maxExtraForLostEvents, extraLostEvents);
          sumExtraLostEvents += extraLostEvents;
        }
      }
      std::cout << "prefix=" << prefix
                << " windows=" << windows
                << " minOld=" << minOld
                << " minShift=" << minShift
                << " maxLost=" << maxLost
                << " maxLostAtSeed#" << (worstLostIndex + 1)
                << " p=" << primes[(std::size_t)worstLostIndex]
                << " avgLost=" << (windows ? sumLost / windows : 0)
                << " maxDrop=" << maxDrop
                << " avgDrop=" << (windows ? sumDrop / windows : 0)
                << " maxExtraOldCount=" << maxExtraForOldCount
                << " avgExtraOldCount=" << (windows > failOldCount ? sumExtraOld / (windows - failOldCount) : 0)
                << " failOldCount=" << failOldCount;
      if (failOldCount) {
        std::cout << " worstOldAtSeed#" << (worstOldIndex + 1)
                  << " p=" << primes[(std::size_t)worstOldIndex];
      }
      std::cout << " maxExtraCap=" << maxExtraForCap
                << " avgExtraCap=" << (windows > failCap ? sumExtraCap / (windows - failCap) : 0)
                << " failCap=" << failCap;
      if (failCap) {
        std::cout << " worstCapAtSeed#" << (worstCapIndex + 1)
                  << " p=" << primes[(std::size_t)worstCapIndex];
      }
      std::cout << " maxExtraLostEvents=" << maxExtraForLostEvents
                << " avgExtraLostEvents=" << (windows > failLostEvents ? sumExtraLostEvents / (windows - failLostEvents) : 0)
                << " failLostEvents=" << failLostEvents;
      if (failLostEvents) {
        std::cout << " worstLostRecoverAtSeed#" << (worstLostRecoverIndex + 1)
                  << " p=" << primes[(std::size_t)worstLostRecoverIndex];
      }
      std::cout << "\n";
    }
    return 0;
  }

  if (coverSeeds != 0) {
    std::vector<u64> strongChildren;
    for (u64 q = 31; q <= coverChildMax; ++q) {
      if (is_prime(q) && leg5(q) && s.reach_unique(q).size() > 95568) {
        strongChildren.push_back(q);
      }
    }
    std::unordered_set<u64> strongSet(strongChildren.begin(), strongChildren.end());
    u64 seenSeeds = 0, uncovered = 0, minStrongHits = ~0ULL, maxStrongHits = 0;
    std::cout << "cover start>=" << start
              << " seeds=" << coverSeeds
              << " strongChildMax=" << coverChildMax
              << " strongChildCount=" << strongChildren.size()
              << "\n";
    for (u64 p = start; seenSeeds < coverSeeds; ++p) {
      if (!is_prime(p) || !leg5(p)) continue;
      ++seenSeeds;
      auto children = s.child_edges(p);
      u64 hits = 0;
      for (u64 q : children) if (strongSet.count(q)) ++hits;
      minStrongHits = std::min(minStrongHits, hits);
      maxStrongHits = std::max(maxStrongHits, hits);
      if (hits == 0) {
        ++uncovered;
        std::cout << "uncovered seed#" << seenSeeds << " p=" << p
                  << " childCount=" << children.size() << "\n";
      }
    }
    std::cout << "summary uncovered=" << uncovered
              << " minStrongHits=" << minStrongHits
              << " maxStrongHits=" << maxStrongHits
              << "\n";
    return 0;
  }

  if (strongChildSeeds != 0) {
    u64 seenSeeds = 0, noStrong = 0, minBest = ~0ULL, minBestP = 0, minBestQ = 0;
    for (u64 p = start; seenSeeds < strongChildSeeds; ++p) {
      if (!is_prime(p) || !leg5(p)) continue;
      ++seenSeeds;
      auto children = s.child_edges(p);
      u64 bestReach = 0, bestQ = 0, strongCount = 0;
      for (u64 q : children) {
        u64 reach = (u64)s.reach_unique(q).size();
        if (reach > bestReach) { bestReach = reach; bestQ = q; }
        if (reach > 95568) ++strongCount;
      }
      if (bestReach <= 95568) ++noStrong;
      if (bestReach < minBest) { minBest = bestReach; minBestP = p; minBestQ = bestQ; }
      std::cout << "seed#" << seenSeeds
                << " p=" << p
                << " childCount=" << children.size()
                << " strongChildren=" << strongCount
                << " bestChild=" << bestQ
                << " bestReach=" << bestReach
                << "\n";
    }
    std::cout << "summary seeds=" << seenSeeds
              << " noStrongChild=" << noStrong
              << " minBestReach=" << minBest
              << " minBestSeed=" << minBestP
              << " minBestChild=" << minBestQ
              << "\n";
    return 0;
  }

  if (childFreqSeeds != 0) {
    std::unordered_map<u64,u64> freq;
    u64 seenSeeds = 0, noChild = 0;
    for (u64 p = start; seenSeeds < childFreqSeeds; ++p) {
      if (!is_prime(p) || !leg5(p)) continue;
      ++seenSeeds;
      auto children = s.child_edges(p);
      if (children.empty()) ++noChild;
      for (u64 q : children) ++freq[q];
    }
    std::vector<std::pair<u64,u64>> items(freq.begin(), freq.end());
    std::sort(items.begin(), items.end(), [](auto a, auto b) {
      if (a.second != b.second) return a.second > b.second;
      return a.first < b.first;
    });
    std::cout << "child-frequency start>=" << start
              << " seeds=" << seenSeeds
              << " noChild=" << noChild
              << " distinctChildren=" << items.size() << "\n";
    std::size_t limit = std::min<std::size_t>(30, items.size());
    for (std::size_t i = 0; i < limit; ++i) {
      auto [q, f] = items[i];
      auto rec = s.reach_unique(q);
      std::cout << "rank=" << (i+1)
                << " child=" << q
                << " freq=" << f
                << " reach=" << rec.size()
                << "\n";
    }
    return 0;
  }

  if (scanSeeds != 0) {
    u64 seenSeeds = 0, minReach = ~0ULL, maxReach = 0, belowCap = 0;
    u64 minP = 0, maxP = 0, prev = 0, maxGap = 0, sumReach = 0;
    for (u64 p = start; seenSeeds < scanSeeds; ++p) {
      if (!is_prime(p) || !leg5(p)) continue;
      ++seenSeeds;
      if (prev != 0) maxGap = std::max(maxGap, p - prev);
      prev = p;
      auto rec = s.reach_unique(p);
      u64 reach = (u64)rec.size();
      sumReach += reach;
      if (reach < minReach) { minReach = reach; minP = p; }
      if (reach > maxReach) { maxReach = reach; maxP = p; }
      if (reach <= 95568) ++belowCap;
    }
    std::cout << "scan start>=" << start
              << " seeds=" << seenSeeds
              << " minReach=" << minReach << " at " << minP
              << " maxReach=" << maxReach << " at " << maxP
              << " avgReach=" << (seenSeeds ? (sumReach / seenSeeds) : 0)
              << " belowOrAtCap=" << belowCap
              << " maxGapBetweenUsableSeeds=" << maxGap
              << "\n";
    return 0;
  }

  if (perSeed != 0) {
    std::unordered_set<int> cumulative;
    u64 seenSeeds = 0, prev = 0;
    std::cout << "per-seed start>=" << start << " limit=" << perSeed
              << " cap=95568 predictedUniverse=" << s.cert.predictedCodes.size() << "\n";
    for (u64 p = start; seenSeeds < perSeed; ++p) {
      if (!is_prime(p) || !leg5(p)) continue;
      ++seenSeeds;
      auto direct = s.target_unique_at(p);
      auto rec = s.reach_unique(p);
      u64 actual = 0, fresh = 0;
      for (int id : rec) {
        u64 code = s.cert.predictedCodes[(std::size_t)id];
        if (s.cert.actualEvents.count(code)) ++actual;
        if (!cumulative.count(id)) ++fresh;
      }
      for (int id : rec) cumulative.insert(id);
      std::cout
        << "seed#" << seenSeeds
        << " p=" << p
        << " gap=" << (prev == 0 ? 0 : p - prev)
        << " directUnique=" << direct.size()
        << " recursiveUnique=" << rec.size()
        << " actualUnique=" << actual
        << " freshVsPrior=" << fresh
        << " cumulativeUnique=" << cumulative.size()
        << "\n";
      prev = p;
    }
    return 0;
  }

  std::unordered_map<int,u64> directAll, recursiveAll;
  std::vector<u64> usedStarts;
  for (u64 p=start; p<=end; ++p) {
    if (!is_prime(p) || !leg5(p)) continue;
    usedStarts.push_back(p);
    merge_raw(directAll, s.target_raw_at(p), s.saturate);
    if (recursive) merge_raw(recursiveAll, s.reach_raw(p), s.saturate);
  }
  auto summarize = [&](const std::unordered_map<int,u64>& m) {
    u64 raw=0, maxf=0, gt2=0, actual=0;
    for (auto& kv : m) {
      raw = (s.saturate - raw < kv.second) ? s.saturate : raw + kv.second;
      maxf = std::max(maxf, kv.second);
      if (kv.second > 2) ++gt2;
      u64 code = s.cert.predictedCodes[(std::size_t)kv.first];
      if (s.cert.actualEvents.count(code)) ++actual;
    }
    return std::array<u64,5>{raw, (u64)m.size(), actual, maxf, gt2};
  };
  auto d = summarize(directAll);
  std::cout << "range=[" << start << "," << end << "] splitPrimeStarts=" << usedStarts.size() << "\n";
  if (!usedStarts.empty()) std::cout << "firstStart=" << usedStarts.front() << " lastStart=" << usedStarts.back() << "\n";
  std::cout << "direct raw=" << d[0] << " unique=" << d[1] << " actualUnique=" << d[2] << " maxFiber=" << d[3] << " fibersGt2=" << d[4] << "\n";
  if (recursive) {
    auto r = summarize(recursiveAll);
    std::cout << "recursive raw=" << r[0] << " unique=" << r[1] << " actualUnique=" << r[2] << " maxFiber=" << r[3] << " fibersGt2=" << r[4] << "\n";
  }
  std::cout << "cap=95568 k2Cap=" << (2ULL*95568ULL) << "\n";
}
