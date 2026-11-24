#!/usr/bin/env python3
"""End-to-end verification tests for the compiled native `maglean` CLI and converter."""

import hashlib
import json
import subprocess
import sys
import tempfile
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BIN = ROOT / ".lake" / "build" / "bin" / "maglean"
CONVERTER = ROOT / "scripts" / "convert_evidence.py"
EXAMPLES = ROOT / "examples"
REGRESSION = ROOT / "Tests" / "regression"
REAL_FIXTURES = EXAMPLES / "real_tool_outputs"


def run_cli(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        [str(BIN), *args],
        capture_output=True,
        text=True,
        check=False,
    )


def run_converter(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, str(CONVERTER), *args],
        capture_output=True,
        text=True,
        check=False,
    )


def parse_frac(s: str) -> Fraction:
    return Fraction(s)


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_hq_ecoli():
    path = EXAMPLES / "hq_ecoli_mag.json"
    res = run_cli("--json", str(path))
    assert res.returncode == 0, res.stderr
    data = json.loads(res.stdout)
    assert data["mag_id"] == "MAG_001_Ecoli_HQ"
    assert data["input_sha256"] == file_sha256(path)
    assert data["maglean_version"] == "0.2.0"
    assert len(data["git_commit"]) >= 7
    assert "4.36.0" in data["lean_toolchain"]
    assert parse_frac(data["completeness_exact"]) == Fraction(1)
    assert parse_frac(data["contamination_exact"]) == Fraction(0)
    assert parse_frac(data["marker_mass_exact"]) == Fraction(1)
    assert data["mimag_tier"] == "High-Quality (MIMAG HQ)"
    assert data["tax_coherent"] is True
    assert data["accessory_contigs"] == 1
    assert data["accessory_bp"] == 95000
    assert data["marker_bearing_contigs"] == 3
    for ra in data["rank_audits"]:
        assert parse_frac(ra["purity_cons"]) == Fraction(1)
        assert parse_frac(ra["chimerism"]) == Fraction(0)
    print("PASS: test_hq_ecoli")


def test_stealth_chimera():
    path = EXAMPLES / "stealth_chimera_mag.json"
    res = run_cli("--json", str(path))
    assert res.returncode == 0, res.stderr
    data = json.loads(res.stdout)
    assert data["input_sha256"] == file_sha256(path)
    assert parse_frac(data["completeness_exact"]) == Fraction(1)
    assert parse_frac(data["contamination_exact"]) == Fraction(0)
    assert data["mimag_tier"] == "High-Quality (MIMAG HQ)"
    assert data["tax_coherent"] is True
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
    assert parse_frac(phylum["purity_drop"]) == Fraction(1, 2)
    assert parse_frac(genus["purity_drop"]) == Fraction(1)
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
    cons_vals = [parse_frac(r["purity_cons"]) for r in data["rank_audits"]]
    assert cons_vals == sorted(cons_vals, reverse=True), f"Non-monotone purityCons: {cons_vals}"
    print("PASS: test_contaminated_mag")


def test_text_reports_provenance_and_ci_flag():
    hq = EXAMPLES / "hq_ecoli_mag.json"
    sc = EXAMPLES / "stealth_chimera_mag.json"
    res = run_cli(str(hq), str(sc))
    assert res.returncode == 0, res.stderr
    assert "MAG_001_Ecoli_HQ" in res.stdout
    assert "MAG_002_Stealth_Chimera" in res.stdout
    assert "STEALTH_CHIMERA_ALERT" in res.stdout
    assert file_sha256(hq) in res.stdout
    assert file_sha256(sc) in res.stdout
    assert "omitted by default (pass --ci" in res.stdout
    assert "kCheckTaxCoherent_sound" in res.stdout

    res_ci = run_cli("--ci", str(hq))
    assert res_ci.returncode == 0, res_ci.stderr
    assert "conditional on independent marker-set detections" in res_ci.stdout

    bad = run_cli(str(EXAMPLES / "nonexistent.json"))
    assert bad.returncode == 2
    print("PASS: test_text_reports_provenance_and_ci_flag")


def test_unclassified_is_not_chimerism():
    res = run_cli("--json", str(REGRESSION / "unclassified_species_single_taxon.json"))
    assert res.returncode == 0, res.stderr
    data = json.loads(res.stdout)
    assert not any("STEALTH_CHIMERA_ALERT" in a for a in data["alerts"]), data["alerts"]
    print("PASS: test_unclassified_is_not_chimerism")


def test_sparse_rank_second_taxon_is_not_chimerism():
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


def test_converter_real_ecoli_mg1655():
    fx = REAL_FIXTURES / "ecoli_mg1655"
    with tempfile.TemporaryDirectory() as tmp:
        out_json = Path(tmp) / "ecoli_mg1655.json"
        conv = run_converter(
            "--mag-id", "GCF_000005845.2_Ecoli_MG1655",
            "--lineage", "d__Bacteria;p__Pseudomonadota;c__Gammaproteobacteria;o__Enterobacterales;f__Enterobacteriaceae;g__Escherichia;s__Escherichia coli",
            "--contigs", str(fx / "contigs.tsv"),
            "--marker-sets", str(REAL_FIXTURES / "bacterial_markers.tsv"),
            "--checkm-hits", str(fx / "checkm_marker_gene_stats.tsv"),
            "--bin-id", "GCF_000005845.2",
            "--taxonomy", str(fx / "contig_taxonomy.tsv"),
            "--barrnap", str(fx / "barrnap.gff"),
            "--trnascan", str(fx / "trnascan.tsv"),
            "-o", str(out_json),
        )
        assert conv.returncode == 0, conv.stderr
        ev = json.loads(out_json.read_text(encoding="utf-8"))
        # All 20 standard amino acids (fMet merged into Met, SeC ignored)
        assert ev["rna"]["distinct_tRNAs"] == 20
        assert ev["rna"]["has_23S"] and ev["rna"]["has_16S"] and ev["rna"]["has_5S"]

        res = run_cli("--json", str(out_json))
        assert res.returncode == 0, res.stderr
        data = json.loads(res.stdout)
        assert data["input_sha256"] == file_sha256(out_json)
        assert data["num_marker_sets"] == 56
        assert parse_frac(data["completeness_exact"]) == Fraction(1)
        assert parse_frac(data["contamination_exact"]) == Fraction(0)
        assert data["mimag_tier"] == "High-Quality (MIMAG HQ)"
        assert data["tax_coherent"] is True
        assert data["alerts"] == [], data["alerts"]
    print("PASS: test_converter_real_ecoli_mg1655")


def test_converter_real_uba_mag():
    fx = REAL_FIXTURES / "uba_mag"
    with tempfile.TemporaryDirectory() as tmp:
        out_json = Path(tmp) / "uba_mag.json"
        conv = run_converter(
            "--mag-id", "UBA10002_Phocaeicola_MAG",
            "--lineage", "d__Bacteria;p__Bacteroidota;c__Bacteroidia;o__Bacteroidales;f__Bacteroidaceae;g__Phocaeicola",
            "--contigs", str(fx / "contigs.tsv"),
            "--marker-sets", str(REAL_FIXTURES / "bacterial_markers.tsv"),
            "--checkm-hits", str(fx / "checkm_marker_gene_stats.tsv"),
            "--bin-id", "UBA10002",
            "--taxonomy", str(fx / "contig_taxonomy.tsv"),
            "--barrnap", str(fx / "barrnap.gff"),
            "--trnascan", str(fx / "trnascan.tsv"),
            "-o", str(out_json),
        )
        assert conv.returncode == 0, conv.stderr
        ev = json.loads(out_json.read_text(encoding="utf-8"))
        # 19 canonical amino acids (pseudo Val and Undet excluded)
        assert ev["rna"]["distinct_tRNAs"] == 19
        assert ev["rna"]["has_16S"] and ev["rna"]["has_23S"] and not ev["rna"]["has_5S"]

        res = run_cli("--json", str(out_json))
        assert res.returncode == 0, res.stderr
        data = json.loads(res.stdout)
        assert data["input_sha256"] == file_sha256(out_json)
        assert parse_frac(data["completeness_exact"]) == Fraction(52, 56)
        assert parse_frac(data["contamination_exact"]) == Fraction(1, 56)
        assert parse_frac(data["marker_mass_exact"]) == Fraction(53, 56)
        # >90% comp & <5% cont, but missing 5S rRNA => downgraded to MQ!
        assert data["mimag_tier"] == "Medium-Quality (MIMAG MQ)"
        assert any("MIMAG_HQ_RNA_DOWNGRADE" in a for a in data["alerts"])
        assert not any("STEALTH_CHIMERA_ALERT" in a for a in data["alerts"])
        assert data["accessory_contigs"] == 1
        assert data["accessory_bp"] == 62100
        assert data["marker_bearing_contigs"] == 5
        assert data["tax_coherent"] is True
    print("PASS: test_converter_real_uba_mag")


def test_converter_strict_rejections():
    fx = REAL_FIXTURES / "ecoli_mg1655"
    with tempfile.TemporaryDirectory() as tmp:
        # 1. Unknown rank prefix (k__Bacteria instead of d__Bacteria)
        bad_tax = Path(tmp) / "bad_tax.tsv"
        bad_tax.write_text("contig_id\tlineage\nNC_000913.3\tk__Bacteria\n", encoding="utf-8")
        res1 = run_converter(
            "--mag-id", "bad1",
            "--contigs", str(fx / "contigs.tsv"),
            "--marker-sets", str(REAL_FIXTURES / "bacterial_markers.tsv"),
            "--checkm-hits", str(fx / "checkm_marker_gene_stats.tsv"),
            "--taxonomy", str(bad_tax),
            "--barrnap", str(fx / "barrnap.gff"),
            "--trnascan", str(fx / "trnascan.tsv"),
        )
        assert res1.returncode == 2
        assert "unknown rank prefix" in res1.stderr

        # 2. Missing contig in taxonomy table
        extra_contigs = Path(tmp) / "extra_contigs.tsv"
        extra_contigs.write_text(
            "contig_id\tlength\nNC_000913.3\t4641652\nNC_EXTRA\t50000\n",
            encoding="utf-8",
        )
        res2 = run_converter(
            "--mag-id", "bad2",
            "--contigs", str(extra_contigs),
            "--marker-sets", str(REAL_FIXTURES / "bacterial_markers.tsv"),
            "--checkm-hits", str(fx / "checkm_marker_gene_stats.tsv"),
            "--taxonomy", str(fx / "contig_taxonomy.tsv"),
            "--barrnap", str(fx / "barrnap.gff"),
            "--trnascan", str(fx / "trnascan.tsv"),
        )
        assert res2.returncode == 2
        assert "missing from taxonomy table" in res2.stderr
    print("PASS: test_converter_strict_rejections")


if __name__ == "__main__":
    if not BIN.exists():
        sys.exit(f"Binary not found: {BIN}")
    test_hq_ecoli()
    test_stealth_chimera()
    test_unclassified_dilution()
    test_patescibacteria_reduced()
    test_contaminated_mag()
    test_text_reports_provenance_and_ci_flag()
    test_unclassified_is_not_chimerism()
    test_sparse_rank_second_taxon_is_not_chimerism()
    test_rejects_unknown_rank_key()
    test_rejects_duplicate_marker_sets()
    test_rejects_zero_length_contig()
    test_converter_real_ecoli_mg1655()
    test_converter_real_uba_mag()
    test_converter_strict_rejections()
    print("\nALL 14 CLI & CONVERTER TESTS PASSED!")
