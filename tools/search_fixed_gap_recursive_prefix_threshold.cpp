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

static vector<u64> primes_upto(u64 n) {
  vector<bool> comp(n + 1, false);
  vector<u64> primes;
  for (u64 p = 2; p <= n; ++p) {
    if (comp[p]) continue;
    primes.push_back(p);
    if (p <= n / p) {
      for (u64 m = p * p; m <= n; m += p) comp[m] = true;
    }
  }
  return primes;
}

struct Family {
  u64 d = 6;
  u64 A = 3;
  u64 B = 4;
  u64 C = 5;
};

static Family family_for_d(u64 d) {
  static const vector<Family> fam = {
    {6,3,4,5}, {24,6,8,10}, {30,5,12,13}, {54,9,12,15},
    {60,8,15,17}, {84,7,24,25}, {96,12,16,20}, {120,10,24,26}
  };
  for (auto f : fam) if (f.d == d) return f;
  throw runtime_error("unsupported d; use one of 6,24,30,54,60,84,96,120");
}

static u64 inv_mod_prime(u64 a, u64 p) {
  return mod_pow(a % p, p - 2, p);
}

struct SlotProfile {
  vector<uint32_t> spf;
  vector<uint32_t> lpf;
};

static SlotProfile build_factor_profile(u64 n) {
  SlotProfile prof;
  prof.spf.assign(n + 1, 0);
  prof.lpf.assign(n + 1, 0);
  for (u64 p = 2; p <= n; ++p) {
    if (prof.spf[p] != 0) continue;
    for (u64 m = p; m <= n; m += p) {
      if (prof.spf[m] == 0) prof.spf[m] = (uint32_t)p;
      prof.lpf[m] = (uint32_t)p;
    }
  }
  return prof;
}

static bool y_smooth(const SlotProfile& prof, u64 n, u64 y) {
  return n <= 1 || prof.lpf[(size_t)n] <= y;
}

static bool z_rough(const SlotProfile& prof, u64 n, u64 z) {
  return n > 1 && prof.spf[(size_t)n] > z;
}

static u64 encode_event(u64 u, int side) {
  return (u << 1) | (u64)side;
}

struct TargetBlock {
  u64 X = 30000000;
  u64 y = 100000;
  u64 z = 300;
  unordered_map<u64,int> predictedEventId;
  vector<u64> predictedCodes;
  unordered_set<u64> actualEvents;
  u64 baseCard = 0;
  u64 actualCap = 0;
  array<u64,2> supportOffsets = {0, 0};
  array<u64,2> middleOffsets = {0, 0};
};

static pair<array<u64,2>, array<u64,2>> orientation_offsets(
    const Family& f, int orientation) {
  switch (orientation) {
    case 0: return {{0, f.B}, {f.A, f.A + f.B}};
    case 1: return {{0, f.A}, {f.B, f.A + f.B}};
    case 2: return {{f.A + f.B, f.A}, {0, f.B}};
    case 3: return {{f.A + f.B, f.B}, {0, f.A}};
    default: throw runtime_error("--orientation must be 0, 1, 2, or 3");
  }
}

static TargetBlock build_target_block(
    const Family& f, u64 X, u64 y, u64 z, int orientation) {
  TargetBlock block;
  block.X = X;
  block.y = y;
  block.z = z;
  auto [supportOffsets, middleOffsets] = orientation_offsets(f, orientation);
  block.supportOffsets = supportOffsets;
  block.middleOffsets = middleOffsets;
  const u64 maxN = X + f.A + f.B + 4;
  auto prof = build_factor_profile(maxN);
  for (u64 u = 1; u + f.A + f.B <= X; ++u) {
    const u64 support0 = u + supportOffsets[0];
    const u64 support1 = u + supportOffsets[1];
    const u64 mid0 = u + middleOffsets[0];
    const u64 mid1 = u + middleOffsets[1];
    if (!y_smooth(prof, support0, y)) continue;
    if (!y_smooth(prof, support1, y)) continue;
    if (!z_rough(prof, mid0, z)) continue;
    if (!z_rough(prof, mid1, z)) continue;
    ++block.baseCard;
    for (int side = 0; side < 2; ++side) {
      u64 code = encode_event(u, side);
      block.predictedEventId.emplace(code, (int)block.predictedEventId.size());
      block.predictedCodes.push_back(code);
    }
    if (y_smooth(prof, mid0, y)) block.actualEvents.insert(encode_event(u, 0));
    if (y_smooth(prof, mid1, y)) block.actualEvents.insert(encode_event(u, 1));
  }
  block.actualCap = block.actualEvents.size();
  return block;
}

struct Row {
  u64 u;
  array<u64,4> vals;
};

struct Search {
  Family f;
  TargetBlock block;
  u64 minChild = 31;
  unordered_map<u64, vector<Row>> rowCache;
  unordered_map<u64, vector<int>> targetCache;
  unordered_map<u64, vector<u64>> childCache;
  unordered_map<u64, vector<int>> reachCache;

  vector<Row> rows_for(u64 p) {
    auto it = rowCache.find(p);
    if (it != rowCache.end()) return it->second;
    vector<Row> out;
    if (p <= 2 || f.C % p == 0) {
      rowCache.emplace(p, out);
      return out;
    }
    const u64 inv2 = inv_mod_prime(2, p);
    const u64 shift = (f.A + f.B) % p;
    for (u64 root : {f.C % p, (p - (f.C % p)) % p}) {
      u64 u = (root + p - shift) % p;
      u = mod_mul(u, inv2, p);
      u128 mid = (u128)u * (u + f.A + f.B) + f.d;
      if (mid % p == 0) {
        u64 h = (u64)(mid / p);
        if (1 <= h && h < p) {
          out.push_back(Row{u, {u, u + f.A, u + f.B, u + f.A + f.B}});
        }
      }
    }
    sort(out.begin(), out.end(), [](const Row& a, const Row& b) {
      return a.u < b.u;
    });
    out.erase(unique(out.begin(), out.end(), [](const Row& a, const Row& b) {
      return a.u == b.u;
    }), out.end());
    rowCache.emplace(p, out);
    return out;
  }

  vector<int> target_events_at(u64 p) {
    auto it = targetCache.find(p);
    if (it != targetCache.end()) return it->second;
    vector<int> ev;
    for (const Row& r : rows_for(p)) {
      if (p < block.X) {
        for (u64 u = r.u; u < block.X; u += p) {
          auto e0 = block.predictedEventId.find(encode_event(u, 0));
          if (e0 != block.predictedEventId.end()) ev.push_back(e0->second);
          auto e1 = block.predictedEventId.find(encode_event(u, 1));
          if (e1 != block.predictedEventId.end()) ev.push_back(e1->second);
        }
      } else if (r.u < block.X) {
        auto e0 = block.predictedEventId.find(encode_event(r.u, 0));
        if (e0 != block.predictedEventId.end()) ev.push_back(e0->second);
        auto e1 = block.predictedEventId.find(encode_event(r.u, 1));
        if (e1 != block.predictedEventId.end()) ev.push_back(e1->second);
      }
    }
    sort(ev.begin(), ev.end());
    ev.erase(unique(ev.begin(), ev.end()), ev.end());
    targetCache.emplace(p, ev);
    return ev;
  }

  vector<u64> child_edges(u64 p) {
    auto it = childCache.find(p);
    if (it != childCache.end()) return it->second;
    vector<u64> out;
    for (const Row& r : rows_for(p)) {
      for (u64 v : r.vals) {
        // The experimental fixed-gap Pythagorean family has no Legendre
        // split restriction.  We keep the child descent deliberately coarse:
        // every smaller prime factor of a routed slot can continue.
        u64 n = v;
        for (u64 q = 2; q <= n / q; ++q) {
          if (n % q != 0) continue;
          if (minChild <= q && q < p && is_prime(q)) out.push_back(q);
          while (n % q == 0) n /= q;
        }
        if (n > 1 && minChild <= n && n < p && is_prime(n)) out.push_back(n);
      }
    }
    sort(out.begin(), out.end(), greater<u64>());
    out.erase(unique(out.begin(), out.end()), out.end());
    childCache.emplace(p, out);
    return out;
  }

  vector<int> reachable_events(u64 p) {
    auto it = reachCache.find(p);
    if (it != reachCache.end()) return it->second;
    vector<int> ev = target_events_at(p);
    for (u64 q : child_edges(p)) {
      auto child = reachable_events(q);
      ev.insert(ev.end(), child.begin(), child.end());
    }
    sort(ev.begin(), ev.end());
    ev.erase(unique(ev.begin(), ev.end()), ev.end());
    reachCache.emplace(p, ev);
    return ev;
  }
};

static void usage(const char* argv0) {
  cerr << "usage: " << argv0 << " --d N [options]\n"
       << "  --d N            one of 6,24,30,54,60,84,96,120\n"
       << "  --X N            target block bound, default 30000000\n"
       << "  --y N            smooth bound, default 100000\n"
       << "  --z N            rough bound, default 300\n"
       << "  --rstart N       first root, default 191265\n"
       << "  --max-span N     root span, default 100000\n"
       << "  --print-every N  status every N prime roots, default 100\n"
       << "  --min-child N    smallest descended child prime, default 31\n";
}

int main(int argc, char** argv) {
  try {
    u64 d = 6, X = 30000000, y = 100000, z = 300;
    u64 rstart = 191265, maxSpan = 100000, printEvery = 100, minChild = 31;
    int orientation = 0;
    for (int i = 1; i < argc; ++i) {
      string a = argv[i];
      auto need = [&]() -> string {
        if (++i >= argc) throw runtime_error("missing value after " + a);
        return argv[i];
      };
      if (a == "--d") d = stoull(need());
      else if (a == "--X") X = stoull(need());
      else if (a == "--y") y = stoull(need());
      else if (a == "--z") z = stoull(need());
      else if (a == "--orientation") orientation = stoi(need());
      else if (a == "--rstart") rstart = stoull(need());
      else if (a == "--max-span") maxSpan = stoull(need());
      else if (a == "--print-every") printEvery = stoull(need());
      else if (a == "--min-child") minChild = stoull(need());
      else if (a == "--help" || a == "-h") { usage(argv[0]); return 0; }
      else throw runtime_error("unknown argument " + a);
    }
    Search search;
    search.f = family_for_d(d);
    search.minChild = minChild;
    cerr << "building target block for d=" << d
         << " A=" << search.f.A << " B=" << search.f.B
         << " C=" << search.f.C << " X=" << X
         << " y=" << y << " z=" << z
         << " orientation=" << orientation << "\n";
    search.block = build_target_block(search.f, X, y, z, orientation);
    cerr << "base=" << search.block.baseCard
         << " actualSideEvents=" << search.block.actualCap
         << " predictedUniverse=" << search.block.predictedCodes.size()
         << " supportOffsets=[" << search.block.supportOffsets[0]
         << "," << search.block.supportOffsets[1] << "]"
         << " middleOffsets=[" << search.block.middleOffsets[0]
         << "," << search.block.middleOffsets[1] << "]"
         << "\n";

    vector<unsigned char> covered(search.block.predictedCodes.size(), 0);
    u64 primeRoots = 0, routedRoots = 0, distinctPredicted = 0;
    u64 distinctActual = 0, distinctFalse = 0;
    auto t0 = chrono::steady_clock::now();
    auto print_status = [&](u64 R, bool finalLine) {
      auto ms = chrono::duration_cast<chrono::milliseconds>(
          chrono::steady_clock::now() - t0).count();
      cout << "{"
           << "\"d\":" << d
           << ",\"gap\":" << 2*d
           << ",\"R\":" << R
           << ",\"span\":" << (R >= rstart ? R - rstart + 1 : 0)
           << ",\"primeRoots\":" << primeRoots
           << ",\"routedRoots\":" << routedRoots
           << ",\"base\":" << search.block.baseCard
           << ",\"actualSideEvents\":" << search.block.actualCap
           << ",\"predictedUniverse\":" << search.block.predictedCodes.size()
           << ",\"distinctPredictedEvents\":" << distinctPredicted
           << ",\"distinctActualPredictedEvents\":" << distinctActual
           << ",\"distinctFalsePredictedEvents\":" << distinctFalse
           << ",\"predictedEventsExceedActualCap\":"
           << (distinctPredicted > search.block.actualCap ? "true" : "false")
           << ",\"elapsedMs\":" << ms
           << ",\"final\":" << (finalLine ? "true" : "false")
           << "}\n";
    };

    u64 nextPrint = printEvery;
    for (u64 R = rstart; R < rstart + maxSpan; ++R) {
      if (!is_prime(R)) continue;
      ++primeRoots;
      auto ev = search.reachable_events(R);
      if (!ev.empty()) {
        ++routedRoots;
        for (int id : ev) {
          if (!covered[(size_t)id]) {
            covered[(size_t)id] = 1;
            ++distinctPredicted;
            u64 code = search.block.predictedCodes[(size_t)id];
            if (search.block.actualEvents.count(code)) ++distinctActual;
            else ++distinctFalse;
          }
        }
      }
      if (primeRoots >= nextPrint) {
        print_status(R, false);
        while (nextPrint <= primeRoots) nextPrint += printEvery;
      }
      if (distinctPredicted > search.block.actualCap) {
        print_status(R, true);
        return 0;
      }
    }
    print_status(rstart + maxSpan - 1, true);
    return distinctPredicted > search.block.actualCap ? 0 : 1;
  } catch (const exception& ex) {
    cerr << "error: " << ex.what() << "\n\n";
    usage(argv[0]);
    return 2;
  }
}
