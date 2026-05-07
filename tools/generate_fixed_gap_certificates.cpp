#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

using u64 = unsigned long long;
using u128 = unsigned __int128;

namespace {

u64 mod_mul(u64 a, u64 b, u64 m) {
  return static_cast<u128>(a) * b % m;
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

std::vector<u64> primes_upto(u64 n) {
  std::vector<bool> composite(n + 1, false);
  std::vector<u64> primes;
  for (u64 p = 2; p <= n; ++p) {
    if (composite[p]) continue;
    primes.push_back(p);
    if (p <= n / p) {
      for (u64 q = p * p; q <= n; q += p) composite[q] = true;
    }
  }
  return primes;
}

struct ResidueKey {
  u64 r_mod;
  u64 d_mod;
  bool operator<(const ResidueKey& o) const {
    return std::tie(r_mod, d_mod) < std::tie(o.r_mod, o.d_mod);
  }
};

constexpr u64 wheel = 2ULL * 3 * 5 * 7 * 11 * 13;
const std::array<u64, 6> wheel_primes = {2, 3, 5, 7, 11, 13};

std::map<ResidueKey, std::vector<u64>> residue_cache;

const std::vector<u64>& allowed_residues(u64 r, u64 d) {
  ResidueKey key{r % wheel, d % wheel};
  auto it = residue_cache.find(key);
  if (it != residue_cache.end()) return it->second;
  std::vector<u64> residues;
  for (u64 h = 0; h < wheel; ++h) {
    bool ok = true;
    for (u64 p : wheel_primes) {
      const u64 x = (r % p) * (h % p) % p;
      const u64 dm = d % p;
      if ((x + p - dm) % p == 0 || (x + dm) % p == 0) {
        ok = false;
        break;
      }
    }
    if (ok) residues.push_back(h);
  }
  auto [pos, _] = residue_cache.emplace(key, std::move(residues));
  return pos->second;
}

bool has_pair_witness(u64 r, u64 d, u64& h_out) {
  if (r <= d + 2) return false;
  const auto& residues = allowed_residues(r, d);
  for (u64 res : residues) {
    u64 h = (res == 0 ? wheel : res);
    for (; h < r; h += wheel) {
      const u64 minus = r * h - d;
      const u64 plus = r * h + d;
      if (is_prime(minus) && is_prime(plus)) {
        h_out = h;
        return true;
      }
    }
  }
  return false;
}

struct Candidate {
  u64 d;
  u64 A;
  u64 B;
  u64 C;
};

struct Result {
  Candidate candidate;
  u64 checked_primes = 0;
  u64 survivor_rows = 0;
  std::vector<u64> failed;
  u64 first_witness_after_last = 0;
};

struct Options {
  u64 last = 127;
  u64 checked_to = 191264;
  std::string json_out =
      "certificates/generated_fixed_gap_certificate_summary.json";
  std::string lean_out =
      "TwinPrimeExternal/GeneratedFixedGapCertificates.lean";
  std::vector<Candidate> candidates = {
      {6, 3, 4, 5},     {24, 6, 8, 10},   {30, 5, 12, 13},
      {54, 9, 12, 15},  {60, 8, 15, 17},  {84, 7, 24, 25},
      {96, 12, 16, 20}, {120, 10, 24, 26}};
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
    std::string arg = argv[i];
    auto need = [&]() -> std::string {
      if (++i >= argc) throw std::runtime_error("missing value after " + arg);
      return argv[i];
    };
    if (arg == "--last") {
      opt.last = parse_u64(need(), arg);
    } else if (arg == "--checked-to") {
      opt.checked_to = parse_u64(need(), arg);
    } else if (arg == "--json-out") {
      opt.json_out = need();
    } else if (arg == "--lean-out") {
      opt.lean_out = need();
    } else if (arg == "--d-list") {
      std::string text = need();
      std::stringstream ss(text);
      std::string part;
      std::vector<Candidate> chosen;
      while (std::getline(ss, part, ',')) {
        if (part.empty()) continue;
        u64 d = parse_u64(part, "--d-list");
        auto it = std::find_if(opt.candidates.begin(), opt.candidates.end(),
                               [&](const Candidate& c) { return c.d == d; });
        if (it == opt.candidates.end()) {
          throw std::runtime_error("d is not a built-in Pythagorean candidate: " +
                                   part);
        }
        chosen.push_back(*it);
      }
      opt.candidates = std::move(chosen);
    } else {
      throw std::runtime_error("unknown argument: " + arg);
    }
  }
  return opt;
}

Result run_candidate(const Candidate& candidate, u64 last, u64 checked_to,
                     const std::vector<u64>& primes) {
  Result result;
  result.candidate = candidate;
  for (u64 r : primes) {
    if (r <= last || checked_to < r || r <= candidate.d + 2) continue;
    ++result.checked_primes;
    u64 h = 0;
    if (has_pair_witness(r, candidate.d, h)) {
      ++result.survivor_rows;
      if (result.first_witness_after_last == 0) {
        result.first_witness_after_last = r * h;
      }
    } else {
      result.failed.push_back(r);
    }
  }
  return result;
}

std::string gap_name(u64 d) {
  return "gap" + std::to_string(2 * d);
}

void write_json(std::ostream& out, const Options& opt,
                const std::vector<Result>& results) {
  out << "{\n";
  out << "  \"mode\": \"fixed-gap-window-certificates\",\n";
  out << "  \"last\": " << opt.last << ",\n";
  out << "  \"checkedTo\": " << opt.checked_to << ",\n";
  out << "  \"candidates\": [\n";
  for (std::size_t i = 0; i < results.size(); ++i) {
    const auto& r = results[i];
    out << "    {\"d\": " << r.candidate.d
        << ", \"gap\": " << 2 * r.candidate.d << ", \"A\": "
        << r.candidate.A << ", \"B\": " << r.candidate.B << ", \"C\": "
        << r.candidate.C << ", \"checkedPrimeRoots\": " << r.checked_primes
        << ", \"survivorRows\": " << r.survivor_rows
        << ", \"failedCount\": " << r.failed.size()
        << ", \"firstWitnessAfterLast\": " << r.first_witness_after_last
        << ", \"success\": " << (r.failed.empty() ? "true" : "false")
        << ", \"failedRoots\": [";
    for (std::size_t j = 0; j < r.failed.size(); ++j) {
      if (j) out << ", ";
      out << r.failed[j];
    }
    out << "]}";
    if (i + 1 != results.size()) out << ",";
    out << "\n";
  }
  out << "  ]\n";
  out << "}\n";
}

void write_lean(std::ostream& out, const Options& opt,
                const std::vector<Result>& results) {
  out << "import TwinPrimeExternal.FixedGap\n\n";
  out << "/-!\n";
  out << "# Generated Fixed-Gap Certificates\n\n";
  out << "Generated by `tools/generate_fixed_gap_certificates.cpp`.\n\n";
  out << "This file records finite midpoint-row scans for the Pythagorean fixed-gap\n";
  out << "candidates up to actual gap `246`.  The finite scan only proves that the\n";
  out << "first fixed-gap exception after `127`, if any, is beyond the checked window.\n";
  out << "The full infinitude endpoint for a fixed gap still requires the corresponding\n";
  out << "external recursive no-tail certificate.\n";
  out << "-/\n\n";
  out << "namespace TwinPrimeExternal.GeneratedFixedGapCertificates\n\n";
  out << "def last : Nat := " << opt.last << "\n";
  out << "def checkedTo : Nat := " << opt.checked_to << "\n\n";
  out << "theorem checkedTo_eq_certificateVerifiedTo :\n";
  out << "    checkedTo = TwinPrimeExternal.certificateVerifiedTo := by\n";
  out << "  norm_num [checkedTo, TwinPrimeExternal.certificateVerifiedTo]\n\n";

  for (const auto& r : results) {
    const std::string name = gap_name(r.candidate.d);
    out << "namespace " << name << "\n\n";
    out << "def d : Nat := " << r.candidate.d << "\n";
    out << "def actualGap : Nat := " << 2 * r.candidate.d << "\n";
    out << "def A : Nat := " << r.candidate.A << "\n";
    out << "def B : Nat := " << r.candidate.B << "\n";
    out << "def C : Nat := " << r.candidate.C << "\n";
    out << "def checkedPrimeRoots : Nat := " << r.checked_primes << "\n";
    out << "def survivorRows : Nat := " << r.survivor_rows << "\n";
    out << "def failedRoots : Nat := " << r.failed.size() << "\n";
    out << "def firstWitnessAfterLast : Nat := "
        << r.first_witness_after_last << "\n\n";
    out << "theorem pythagorean_family :\n";
    out << "    A * B = 2 * d /\\ A ^ 2 + B ^ 2 = C ^ 2 := by\n";
    out << "  norm_num [A, B, C, d]\n\n";
    out << "theorem actualGap_eq : actualGap = 2 * d := by\n";
    out << "  norm_num [actualGap, d]\n\n";
    out << "theorem actualGap_le_246 : actualGap <= 246 := by\n";
    out << "  norm_num [actualGap]\n\n";
    out << "theorem failedRoots_eq_zero : failedRoots = 0 := by\n";
    if (r.failed.empty()) {
      out << "  rfl\n\n";
    } else {
      out << "  norm_num [failedRoots]\n\n";
    }
    out << "/-- Trusted external finite scan for this fixed gap. -/\n";
    out << "axiom external_exceptionFree_to_certificateThreshold :\n";
    out << "    TwinPrimeExternal.ExceptionFreeUpTo\n";
    out << "      (TwinPrimeExternal.FixedGapExceptionalPrime d)\n";
    out << "      TwinPrimeExternal.certificateVerifiedTo\n\n";
    out << "theorem any_firstException_after_127_occurs_after_certificateThreshold\n";
    out << "    (firstException :\n";
    out << "      TwinPrimeExternal.FirstExceptionAfterLastObserved\n";
    out << "        (TwinPrimeExternal.FixedGapExceptionalPrime d)) :\n";
    out << "    TwinPrimeExternal.certificateVerifiedTo < firstException.r :=\n";
    out << "  TwinPrimeExternal.firstExceptionAfterLast_occurs_after_certificateThreshold_of_exceptionFreeUpTo\n";
    out << "    external_exceptionFree_to_certificateThreshold firstException\n\n";
    out << "/--\n";
    out << "Total fixed-gap endpoint status for this candidate.  This theorem is\n";
    out << "conditional until a recursive no-cofinal-tail certificate is generated for\n";
    out << "this exact fixed gap.\n";
    out << "-/\n";
    out << "theorem arbitrarily_large_pairs_of_no_tail\n";
    out << "    (hno :\n";
    out << "      Not (exists K,\n";
    out << "        TwinPrimeExternal.CofinalExceptionTail\n";
    out << "          (TwinPrimeExternal.FixedGapExceptionalPrime d) K)) :\n";
    out << "    TwinPrimeExternal.ArbitrarilyLargeFixedGapPrimePairs d :=\n";
    out << "  TwinPrimeExternal.arbitrarily_large_fixedGapPairs_of_no_cofinalExceptionTail\n";
    out << "    hno\n\n";
    out << "end " << name << "\n\n";
  }

  out << "end TwinPrimeExternal.GeneratedFixedGapCertificates\n";
}

}  // namespace

int main(int argc, char** argv) {
  try {
    Options opt = parse_options(argc, argv);
    const auto primes = primes_upto(opt.checked_to);
    std::vector<Result> results;
    for (const auto& candidate : opt.candidates) {
      results.push_back(run_candidate(candidate, opt.last, opt.checked_to, primes));
    }

    write_json(std::cout, opt, results);

    if (!opt.json_out.empty()) {
      std::ofstream json(opt.json_out);
      if (!json) throw std::runtime_error("could not open JSON output");
      write_json(json, opt, results);
    }
    if (!opt.lean_out.empty()) {
      std::ofstream lean(opt.lean_out);
      if (!lean) throw std::runtime_error("could not open Lean output");
      write_lean(lean, opt, results);
    }

    bool ok = true;
    for (const auto& result : results) {
      ok = ok && result.failed.empty();
    }
    return ok ? 0 : 1;
  } catch (const std::exception& ex) {
    std::cerr << "error: " << ex.what() << "\n";
    return 2;
  }
}
