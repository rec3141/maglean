#!/usr/bin/env python3
"""Strict converter from standard bioinformatics QC tool outputs to MAGLean JSON.

NOTE: This converter is outside the formally verified Lean kernel. To prevent
silent data corruption before verification, it rejects unknown taxonomy ranks,
duplicate contig IDs, zero-length contigs, and any contig missing from the
assembly/taxonomy tables instead of silently dropping records.

Supported inputs:
  - Contigs: FASTA (.fa/.fna/.fasta) or 2-column TSV (contig_id<TAB>length)
  - Marker sets: TSV (one collocated set per line, comma-separated marker IDs)
    or JSON array of arrays
  - Marker hits: 2-column TSV (contig_id<TAB>marker_id) or CheckM
    marker_gene_stats.tsv format
  - Contig taxonomy: 2-column GTDB-style TSV (contig_id<TAB>d__...;p__...)
    or 8-column headered TSV (contig_id, domain, phylum, class, order, family,
    genus, species)
  - rRNA calls: barrnap GFF3
  - tRNA calls: tRNAscan-SE tabular output (counts distinct standard 20 amino-acid
    isotypes per Bowers et al. 2017 MIMAG)
"""

from __future__ import annotations

import argparse
import ast
import json
import re
import sys
from pathlib import Path
from typing import Dict, List, Optional, Tuple

RANKS = ("domain", "phylum", "class", "order", "family", "genus", "species")
PREFIX_TO_RANK = {
    "d__": "domain",
    "p__": "phylum",
    "c__": "class",
    "o__": "order",
    "f__": "family",
    "g__": "genus",
    "s__": "species",
}
STANDARD_20_AA = {
    "Ala", "Arg", "Asn", "Asp", "Cys",
    "Gln", "Glu", "Gly", "His", "Ile",
    "Leu", "Lys", "Met", "Phe", "Pro",
    "Ser", "Thr", "Trp", "Tyr", "Val",
}
# Standard initiator/elongator Met aliases emitted by tRNAscan-SE
TRNA_AA_ALIASES = {"iMet": "Met", "fMet": "Met", "Ile2": "Ile"}
TRNA_NONSTANDARD_OK = {"SeC", "Sup", "Undet", "Pseudo", "Pyl"}


class ConverterError(ValueError):
    """Raised whenever an input record cannot be mapped strictly."""


def parse_contigs(path: Path) -> Dict[str, int]:
    text = path.read_text(encoding="utf-8")
    lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
    if not lines:
        raise ConverterError(f"Empty contigs file: {path}")

    contigs: Dict[str, int] = {}
    if lines[0].startswith(">"):
        curr_id: Optional[str] = None
        curr_len = 0
        for ln in lines:
            if ln.startswith(">"):
                if curr_id is not None:
                    if curr_len <= 0:
                        raise ConverterError(f"Zero-length contig in FASTA: {curr_id}")
                    contigs[curr_id] = curr_len
                cid = ln[1:].split()[0]
                if not cid:
                    raise ConverterError("Empty FASTA header")
                if cid in contigs:
                    raise ConverterError(f"Duplicate contig ID in FASTA: {cid}")
                curr_id = cid
                curr_len = 0
            else:
                curr_len += len(ln)
        if curr_id is not None:
            if curr_len <= 0:
                raise ConverterError(f"Zero-length contig in FASTA: {curr_id}")
            contigs[curr_id] = curr_len
    else:
        for idx, ln in enumerate(lines, start=1):
            if ln.startswith("#"):
                continue
            parts = ln.split("\t")
            if idx == 1 and parts[0].lower() in {"contig", "contig_id", "id", "scaffold"}:
                continue
            if len(parts) != 2:
                raise ConverterError(
                    f"{path}:{idx}: expected 2 tab-separated columns (contig_id, length)"
                )
            cid, raw_len = parts[0].strip(), parts[1].strip()
            if not cid:
                raise ConverterError(f"{path}:{idx}: empty contig ID")
            if cid in contigs:
                raise ConverterError(f"{path}:{idx}: duplicate contig ID '{cid}'")
            try:
                length = int(raw_len)
            except ValueError as exc:
                raise ConverterError(
                    f"{path}:{idx}: non-integer length '{raw_len}'"
                ) from exc
            if length <= 0:
                raise ConverterError(f"{path}:{idx}: contig '{cid}' length must be positive")
            contigs[cid] = length

    if not contigs:
        raise ConverterError(f"No contigs parsed from {path}")
    return contigs


def parse_marker_sets(path: Path) -> List[List[str]]:
    text = path.read_text(encoding="utf-8").strip()
    if not text:
        raise ConverterError(f"Empty marker_sets file: {path}")
    if text.startswith("["):
        data = json.loads(text)
        if not isinstance(data, list) or not data:
            raise ConverterError("JSON marker_sets must be a nonempty array")
        out: List[List[str]] = []
        for s in data:
            if not isinstance(s, list) or not s or not all(isinstance(g, str) and g for g in s):
                raise ConverterError("Each marker set must be a nonempty list of strings")
            out.append(s)
        return out

    sets: List[List[str]] = []
    for idx, raw in enumerate(text.splitlines(), start=1):
        ln = raw.strip()
        if not ln or ln.startswith("#"):
            continue
        genes = [g.strip() for g in ln.split(",") if g.strip()]
        if not genes:
            raise ConverterError(f"{path}:{idx}: empty collocated marker set")
        sets.append(genes)
    if not sets:
        raise ConverterError(f"No marker sets parsed from {path}")
    return sets


def parse_marker_hits(
    path: Path,
    valid_contigs: Dict[str, int],
    bin_id: Optional[str] = None,
) -> Dict[str, List[str]]:
    hits: Dict[str, List[str]] = {cid: [] for cid in valid_contigs}
    lines = [ln.rstrip("\n") for ln in path.read_text(encoding="utf-8").splitlines() if ln.strip()]
    if not lines:
        return hits

    # Detect CheckM marker_gene_stats.tsv: "<bin_id>\t{'gene_id': {'PF00177': {...}}, ...}"
    first_parts = lines[0].split("\t")
    if len(first_parts) == 2 and first_parts[1].lstrip().startswith("{"):
        matched_bin = False
        for idx, ln in enumerate(lines, start=1):
            parts = ln.split("\t")
            if len(parts) != 2:
                raise ConverterError(f"{path}:{idx}: malformed CheckM marker_gene_stats line")
            row_bin, dict_str = parts[0].strip(), parts[1].strip()
            if bin_id is not None and row_bin != bin_id:
                continue
            matched_bin = True
            try:
                gene_map = ast.literal_eval(dict_str)
            except Exception as exc:
                raise ConverterError(
                    f"{path}:{idx}: failed to parse CheckM dict"
                ) from exc
            if not isinstance(gene_map, dict):
                raise ConverterError(f"{path}:{idx}: expected dict in column 2")
            for orf_id, markers in gene_map.items():
                # Prodigal ORF IDs look like "<contig_id>_<orf_num>"
                if orf_id in valid_contigs:
                    cid = orf_id
                elif "_" in orf_id and orf_id.rsplit("_", 1)[0] in valid_contigs:
                    cid = orf_id.rsplit("_", 1)[0]
                else:
                    raise ConverterError(
                        f"{path}:{idx}: ORF/contig '{orf_id}' not found in contigs table"
                    )
                if not isinstance(markers, dict):
                    raise ConverterError(f"{path}:{idx}: expected marker dict for '{orf_id}'")
                for marker_id in markers.keys():
                    hits[cid].append(str(marker_id))
        if bin_id is not None and not matched_bin:
            raise ConverterError(f"Bin '{bin_id}' not found in CheckM file {path}")
        return hits

    # Standard 2-column TSV: contig_id<TAB>marker_id
    for idx, ln in enumerate(lines, start=1):
        if ln.startswith("#"):
            continue
        parts = ln.split("\t")
        if idx == 1 and parts[0].lower() in {"contig", "contig_id", "id"}:
            continue
        if len(parts) != 2:
            raise ConverterError(
                f"{path}:{idx}: expected 2 tab-separated columns (contig_id, marker_id)"
            )
        cid, marker = parts[0].strip(), parts[1].strip()
        if cid not in valid_contigs:
            raise ConverterError(f"{path}:{idx}: contig '{cid}' missing from contigs table")
        if not marker:
            raise ConverterError(f"{path}:{idx}: empty marker ID")
        hits[cid].append(marker)
    return hits


def parse_gtdb_lineage(lineage: str, context: str) -> Dict[str, str]:
    tax: Dict[str, str] = {}
    if not lineage or lineage.lower() in {"unclassified", "root", "none", "-"}:
        return tax
    for token in lineage.split(";"):
        tok = token.strip()
        if not tok:
            continue
        if len(tok) < 3 or tok[:3] not in PREFIX_TO_RANK:
            raise ConverterError(
                f"{context}: unknown rank prefix in '{tok}'; expected one of {sorted(PREFIX_TO_RANK)}"
            )
        rank = PREFIX_TO_RANK[tok[:3]]
        name = tok[3:].strip()
        if rank in tax:
            raise ConverterError(f"{context}: duplicate rank '{rank}'")
        if name:
            tax[rank] = name
    return tax


def parse_taxonomy(path: Path, valid_contigs: Dict[str, int]) -> Dict[str, Dict[str, str]]:
    lines = [ln.rstrip("\n") for ln in path.read_text(encoding="utf-8").splitlines() if ln.strip()]
    if not lines:
        raise ConverterError(f"Empty taxonomy file: {path}")

    tax_by_contig: Dict[str, Dict[str, str]] = {}
    header_parts = lines[0].split("\t")
    if len(header_parts) >= 3 and header_parts[0].lower() in {"contig", "contig_id", "id"}:
        rank_cols = [c.strip() for c in header_parts[1:]]
        for col in rank_cols:
            if col not in RANKS:
                raise ConverterError(
                    f"{path}:1: unknown taxonomy rank column '{col}'; expected subset of {RANKS}"
                )
        for idx, ln in enumerate(lines[1:], start=2):
            if ln.startswith("#"):
                continue
            parts = ln.split("\t")
            if len(parts) != len(header_parts):
                raise ConverterError(
                    f"{path}:{idx}: expected {len(header_parts)} columns, got {len(parts)}"
                )
            cid = parts[0].strip()
            if cid not in valid_contigs:
                raise ConverterError(f"{path}:{idx}: contig '{cid}' missing from contigs table")
            if cid in tax_by_contig:
                raise ConverterError(f"{path}:{idx}: duplicate contig '{cid}' in taxonomy table")
            entry: Dict[str, str] = {}
            for col, val in zip(rank_cols, parts[1:]):
                v = val.strip()
                if v and v.lower() not in {"na", "none", "unclassified", "-"}:
                    entry[col] = v
            tax_by_contig[cid] = entry
    else:
        for idx, ln in enumerate(lines, start=1):
            if ln.startswith("#"):
                continue
            parts = ln.split("\t")
            if idx == 1 and parts[0].lower() in {"contig", "contig_id", "id"}:
                continue
            if len(parts) != 2:
                raise ConverterError(
                    f"{path}:{idx}: expected 2 columns (contig_id, GTDB lineage)"
                )
            cid, lin = parts[0].strip(), parts[1].strip()
            if cid not in valid_contigs:
                raise ConverterError(f"{path}:{idx}: contig '{cid}' missing from contigs table")
            if cid in tax_by_contig:
                raise ConverterError(f"{path}:{idx}: duplicate contig '{cid}' in taxonomy table")
            tax_by_contig[cid] = parse_gtdb_lineage(lin, f"{path}:{idx}")

    missing = sorted(set(valid_contigs) - set(tax_by_contig))
    if missing:
        raise ConverterError(
            f"Contigs present in contigs table but missing from taxonomy table: {missing[:5]}"
        )
    return tax_by_contig


def parse_barrnap_gff(path: Path, valid_contigs: Dict[str, int]) -> Tuple[bool, bool, bool]:
    has_23s = has_16s = has_5s = False
    for idx, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        ln = raw.strip()
        if not ln or ln.startswith("#"):
            continue
        parts = ln.split("\t")
        if len(parts) != 9:
            raise ConverterError(f"{path}:{idx}: expected 9 GFF3 columns, got {len(parts)}")
        seqid, ftype, attrs = parts[0], parts[2], parts[8]
        if seqid not in valid_contigs:
            raise ConverterError(f"{path}:{idx}: GFF3 seqid '{seqid}' missing from contigs table")
        if ftype != "rRNA":
            continue
        m = re.search(r"(?:^|;)Name=([^;]+)", attrs)
        if not m:
            raise ConverterError(f"{path}:{idx}: rRNA GFF3 record missing Name= attribute")
        name = m.group(1)
        if name.startswith("23S"):
            has_23s = True
        elif name.startswith("16S"):
            has_16s = True
        elif name.startswith("5S"):
            has_5s = True
        else:
            raise ConverterError(f"{path}:{idx}: unrecognized rRNA Name='{name}'")
    return has_23s, has_16s, has_5s


def parse_trnascan_tsv(path: Path, valid_contigs: Dict[str, int]) -> int:
    aa_found = set()
    for idx, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        ln = raw.strip()
        if not ln or ln.startswith("#") or ln.startswith("Sequence") or ln.startswith("Name") or ln.startswith("---"):
            continue
        parts = ln.split("\t")
        if len(parts) < 5:
            raise ConverterError(
                f"{path}:{idx}: expected tRNAscan-SE tabular row with >=5 tab columns"
            )
        seqid = parts[0].strip()
        if seqid not in valid_contigs:
            raise ConverterError(f"{path}:{idx}: tRNA contig '{seqid}' missing from contigs table")
        aa = parts[4].strip()
        note = parts[9].strip().lower() if len(parts) >= 10 else ""
        if "pseudo" in note:
            continue
        aa_norm = TRNA_AA_ALIASES.get(aa, aa)
        if aa_norm in STANDARD_20_AA:
            aa_found.add(aa_norm)
        elif aa_norm in TRNA_NONSTANDARD_OK:
            continue
        else:
            raise ConverterError(f"{path}:{idx}: unrecognized tRNA isotype '{aa}'")
    return len(aa_found)


def build_evidence(args: argparse.Namespace) -> dict:
    contigs = parse_contigs(Path(args.contigs))
    marker_sets = parse_marker_sets(Path(args.marker_sets))
    hits = parse_marker_hits(Path(args.checkm_hits), contigs, bin_id=args.bin_id)
    tax = parse_taxonomy(Path(args.taxonomy), contigs)
    has_23s, has_16s, has_5s = parse_barrnap_gff(Path(args.barrnap), contigs)
    distinct_trnas = parse_trnascan_tsv(Path(args.trnascan), contigs)

    high_id, total_mc = 0, 0
    if args.strain_pairs:
        parts = args.strain_pairs.split(":")
        if len(parts) != 2:
            raise ConverterError("--strain-pairs must be formatted as HIGH:TOTAL")
        high_id, total_mc = int(parts[0]), int(parts[1])
        if high_id < 0 or total_mc < 0 or high_id > total_mc:
            raise ConverterError("Invalid --strain-pairs values")

    contig_list = [
        {
            "id": cid,
            "length": contigs[cid],
            "markers": hits[cid],
            "taxonomy": tax[cid],
        }
        for cid in contigs
    ]
    return {
        "mag_id": args.mag_id,
        "lineage": args.lineage,
        "marker_sets": marker_sets,
        "rna": {
            "has_23S": has_23s,
            "has_16S": has_16s,
            "has_5S": has_5s,
            "distinct_tRNAs": distinct_trnas,
        },
        "strain_heterogeneity": {
            "high_identity_pairs": high_id,
            "total_multicopy_pairs": total_mc,
        },
        "contigs": contig_list,
    }


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Strictly convert CheckM + contig taxonomy + barrnap + tRNAscan-SE outputs to MAGLean JSON."
    )
    parser.add_argument("--mag-id", required=True, help="Identifier for the MAG or genome")
    parser.add_argument("--lineage", default="unclassified", help="Assigned lineage string")
    parser.add_argument("--contigs", required=True, help="Assembly FASTA or contig_id<TAB>length TSV")
    parser.add_argument("--marker-sets", required=True, help="Collocated marker sets (TSV or JSON)")
    parser.add_argument("--checkm-hits", required=True, help="CheckM marker_gene_stats.tsv or contig<TAB>marker TSV")
    parser.add_argument("--bin-id", default=None, help="Bin ID to extract if using multi-bin CheckM marker_gene_stats.tsv")
    parser.add_argument("--taxonomy", required=True, help="Contig taxonomy TSV (GTDB lineage or rank columns)")
    parser.add_argument("--barrnap", required=True, help="barrnap GFF3 rRNA annotations")
    parser.add_argument("--trnascan", required=True, help="tRNAscan-SE tabular output")
    parser.add_argument("--strain-pairs", default=None, help="Optional HIGH:TOTAL multi-copy pair counts")
    parser.add_argument("-o", "--output", default="-", help="Output JSON path (default: stdout)")

    args = parser.parse_args(argv)
    try:
        evidence = build_evidence(args)
    except ConverterError as exc:
        print(f"Converter error: {exc}", file=sys.stderr)
        return 2

    rendered = json.dumps(evidence, indent=2) + "\n"
    if args.output == "-":
        sys.stdout.write(rendered)
    else:
        Path(args.output).write_text(rendered, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
