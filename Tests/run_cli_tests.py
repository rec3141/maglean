#!/usr/bin/env python3
"""End-to-end verification tests for the compiled native `maglean` CLI."""

import json
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BIN = ROOT / ".lake" / "build" / "bin" / "maglean"
EXAMPLES = ROOT / "examples"


def run_cli(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        [str(BIN), *args],
        capture_output=True,
        text=True,
        check=False,
    )


def parse_frac(s: str) -> Fraction:
    return Fraction(s)


def test_hq_ecoli():
    res = run_cli("--json", str(EXAMPLES / "hq_ecoli_mag.json"))
    assert res.returncode == 0, res.stderr
    data = json.loads(res.stdout)
    assert data["mag_id"] == "MAG_001_Ecoli_HQ"
    assert parse_frac(data["completeness_exact"]) == Fraction(1)
    assert parse_frac(data["contamination_exact"]) == Fraction(0)
    assert parse_frac(data["marker_mass_exact"]) == Fraction(1)
    assert data["mimag_tier"] == "High-Quality (MIMAG HQ)"
    assert data["tax_coherent"] is True
    assert data["accessory_contigs"] == 1
    assert data["accessory_bp"] == 95000
    for ra in data["rank_audits"]:
        assert parse_frac(ra["purity_cons"]) == Fraction(1)
        assert parse_frac(ra["chimerism"]) == Fraction(0)
    print("PASS: test_hq_ecoli")


def test_stealth_chimera():
    res = run_cli("--json", str(EXAMPLES / "stealth_chimera_mag.json"))
    assert res.returncode == 0, res.stderr
    data = json.loads(res.stdout)
    # 100% complete, 0% contaminated — passes marker-only CheckM HQ!
    assert parse_frac(data["completeness_exact"]) == Fraction(1)
    assert parse_frac(data["contamination_exact"]) == Fraction(0)
    assert data["mimag_tier"] == "High-Quality (MIMAG HQ)"
    assert data["tax_coherent"] is True
    # Caught by verified taxonomic chimerism audit!
    phylum = next(r for r in data["rank_audits"] if r["rank"] == "phylum")
    assert parse_frac(phylum["purity_cons"]) == Fraction(1, 2)
    assert parse_frac(phylum["chimerism"]) == Fraction(1, 2)
    assert any("STEALTH_CHIMERA_ALERT" in a for a in data["alerts"])
    print("PASS: test_stealth_chimera")


def test_unclassified_dilution():
    res = run_cli("--json", str(EXAMPLES / "unclassified_dilution_mag.json"))
    assert res.returncode == 0, res.stderr
    data = json.loads(res.stdout)
    assert data["tax_coherent"] is True
    phylum = next(r for r in data["rank_audits"] if r["rank"] == "phylum")
    genus = next(r for r in data["rank_audits"] if r["rank"] == "genus")
    # Drop-unclassified purity jumps artificially from 1/2 to 1!
    assert parse_frac(phylum["purity_drop"]) == Fraction(1, 2)
    assert parse_frac(genus["purity_drop"]) == Fraction(1)
    # Conservative purity stays honestly at 1/2, sandwich interval [1/2, 1]!
    assert parse_frac(genus["purity_cons"]) == Fraction(1, 2)
    assert parse_frac(genus["purity_opt"]) == Fraction(1)
    assert parse_frac(genus["unclassified_frac"]) == Fraction(1, 2)
    assert any("UNCLASSIFIED_DILUTION_ALERT" in a for a in data["alerts"])
    print("PASS: test_unclassified_dilution")


def test_patescibacteria_reduced():
    res = run_cli("--json", str(EXAMPLES / "patescibacteria_reduced_mag.json"))
    assert res.returncode == 0, res.stderr
    data = json.loads(res.stdout)
    assert parse_frac(data["completeness_exact"]) == Fraction(7, 10)
    assert parse_frac(data["contamination_exact"]) == Fraction(0)
    assert data["mimag_tier"] == "Medium-Quality (MIMAG MQ)"
    assert data["tax_coherent"] is True
    # Check conservation law holds exactly
    assert parse_frac(data["completeness_exact"]) + parse_frac(data["contamination_exact"]) == parse_frac(data["marker_mass_exact"])
    print("PASS: test_patescibacteria_reduced")


def test_contaminated_mag():
    res = run_cli("--json", str(EXAMPLES / "contaminated_mag.json"))
    assert res.returncode == 0, res.stderr
    data = json.loads(res.stdout)
    assert parse_frac(data["completeness_exact"]) == Fraction(1)
    assert parse_frac(data["contamination_exact"]) == Fraction(3, 10)
    assert parse_frac(data["marker_mass_exact"]) == Fraction(13, 10)
    assert parse_frac(data["composite_q5_exact"]) == Fraction(1) - 5 * Fraction(3, 10)
    assert parse_frac(data["strain_heterogeneity_exact"]) == Fraction(1, 4)
    assert data["mimag_tier"] == "Contaminated (Failed MIMAG <10% Cont)"
    # Check rank-refinement monotonicity: purityCons is non-increasing from domain to species
    cons_vals = [parse_frac(r["purity_cons"]) for r in data["rank_audits"]]
    assert cons_vals == sorted(cons_vals, reverse=True), f"Non-monotone purityCons: {cons_vals}"
    print("PASS: test_contaminated_mag")


def test_text_reports_and_errors():
    res = run_cli(
        str(EXAMPLES / "hq_ecoli_mag.json"),
        str(EXAMPLES / "stealth_chimera_mag.json"),
    )
    assert res.returncode == 0, res.stderr
    assert "MAG_001_Ecoli_HQ" in res.stdout
    assert "MAG_002_Stealth_Chimera" in res.stdout
    assert "STEALTH_CHIMERA_ALERT" in res.stdout

    bad = run_cli(str(EXAMPLES / "nonexistent.json"))
    assert bad.returncode == 2
    print("PASS: test_text_reports_and_errors")


REGRESSION = ROOT / "Tests" / "regression"


def test_unclassified_is_not_chimerism():
    # One taxon; species label on 10% of bp, rest unclassified at species.
    res = run_cli("--json", str(REGRESSION / "unclassified_species_single_taxon.json"))
    assert res.returncode == 0, res.stderr
    data = json.loads(res.stdout)
    assert not any("STEALTH_CHIMERA_ALERT" in a for a in data["alerts"]), data["alerts"]
    print("PASS: test_unclassified_is_not_chimerism")


def test_sparse_rank_second_taxon_is_not_chimerism():
    # 3.99 Mb unclassified at genus/species; 5 kb E. coli and 5 kb Salmonella (Meridian).
    res = run_cli("--json", str(REGRESSION / "sparse_rank_two_taxa.json"))
    assert res.returncode == 0, res.stderr
    data = json.loads(res.stdout)
    assert not any("STEALTH_CHIMERA_ALERT" in a for a in data["alerts"]), data["alerts"]
    print("PASS: test_sparse_rank_second_taxon_is_not_chimerism")


def test_rejects_unknown_rank_key():
    res = run_cli("--json", str(REGRESSION / "capitalised_rank_keys.json"))
    assert res.returncode == 2, res.stdout
    assert "Unknown taxonomy rank" in res.stderr
    print("PASS: test_rejects_unknown_rank_key")


def test_rejects_duplicate_marker_sets():
    res = run_cli("--json", str(REGRESSION / "duplicate_marker_sets.json"))
    assert res.returncode == 2, res.stdout
    assert "duplicate marker sets" in res.stderr
    print("PASS: test_rejects_duplicate_marker_sets")


def test_rejects_zero_length_contig():
    res = run_cli("--json", str(REGRESSION / "zero_length_contig.json"))
    assert res.returncode == 2, res.stdout
    assert "contig length must be positive" in res.stderr
    print("PASS: test_rejects_zero_length_contig")


if __name__ == "__main__":
    if not BIN.exists():
        sys.exit(f"Binary not found: {BIN}")
    test_hq_ecoli()
    test_stealth_chimera()
    test_unclassified_dilution()
    test_patescibacteria_reduced()
    test_contaminated_mag()
    test_text_reports_and_errors()
    test_unclassified_is_not_chimerism()
    test_sparse_rank_second_taxon_is_not_chimerism()
    test_rejects_unknown_rank_key()
    test_rejects_duplicate_marker_sets()
    test_rejects_zero_length_contig()
    print("\nALL CLI TESTS PASSED!")
