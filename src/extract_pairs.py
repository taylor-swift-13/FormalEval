#!/usr/bin/env python3
import argparse
import ast
import gzip
import io
import json
import os
import re
import sys
from typing import Any, Dict, List, Tuple


class HumanEvalPairs:
    def __init__(self, path: str):
        self.path = path
        self.rows: List[Dict[str, Any]] = self._load_jsonl(path)
        if not self.rows:
            raise ValueError('empty or invalid JSONL')

    @staticmethod
    def _open_maybe_gzip(path: str) -> io.TextIOBase:
        if path.endswith('.gz'):
            return io.TextIOWrapper(gzip.open(path, 'rb'), encoding='utf-8')
        return open(path, 'r', encoding='utf-8')

    @classmethod
    def _load_jsonl(cls, path: str) -> List[Dict[str, Any]]:
        rows: List[Dict[str, Any]] = []
        with cls._open_maybe_gzip(path) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    obj = json.loads(line)
                except json.JSONDecodeError:
                    continue
                if isinstance(obj, dict):
                    rows.append(obj)
        return rows

    @staticmethod
    def _extract_tests_str(obj: Dict[str, Any]) -> str:
        for key in ('tests', 'test', 'unit_tests', 'test_code', 'prompt_tests', 'check'):
            v = obj.get(key)
            if isinstance(v, str) and v.strip():
                return v
        plus = obj.get('plus')
        if isinstance(plus, dict):
            v = plus.get('tests')
            if isinstance(v, str) and v.strip():
                return v
        return ''

    @staticmethod
    def _collect_list_literal(lines: List[str], start_idx: int) -> Tuple[str, int]:
        """Collect a Python list literal spanning multiple lines starting from a line
        containing '=' and the first '[' after it. Returns (literal_text, next_index).
        Raises ValueError if cannot parse balanced brackets.
        """
        line = lines[start_idx]
        eq_pos = line.find('=')
        if eq_pos == -1:
            raise ValueError('missing = in declaration line')
        rest = line[eq_pos + 1 :]
        buf: List[str] = []
        depth = 0
        started = False

        def feed_chunk(chunk: str):
            nonlocal depth, started
            for ch in chunk:
                if ch == '[':
                    depth += 1
                    started = True
                elif ch == ']':
                    depth -= 1
            buf.append(chunk)

        feed_chunk(rest)
        i = start_idx + 1
        while (not started) or depth > 0:
            if i >= len(lines):
                raise ValueError('unterminated list literal')
            feed_chunk('\n' + lines[i])
            i += 1
        literal = ''.join(buf).strip()
        last_close = literal.rfind(']')
        if last_close != -1:
            literal = literal[: last_close + 1]
        return literal, i

    @classmethod
    def _parse_inputs_results(cls, tests: str) -> Tuple[List[Any], List[Any]]:
        lines = tests.splitlines()
        inp_idx = next((i for i, ln in enumerate(lines) if re.search(r'^\s*inputs\s*=\s*\[', ln)), None)
        out_idx = next((i for i, ln in enumerate(lines) if re.search(r'^\s*results\s*=\s*\[', ln)), None)
        if inp_idx is None or out_idx is None:
            raise ValueError('inputs/results not found in tests field')
        inputs_str, _ = cls._collect_list_literal(lines, inp_idx)
        results_str, _ = cls._collect_list_literal(lines, out_idx)
        try:
            inputs = ast.literal_eval(inputs_str)
            results = ast.literal_eval(results_str)
        except Exception as e:
            raise ValueError(f'failed to parse inputs/results as Python literals: {e}')
        if not isinstance(inputs, list) or not isinstance(results, list):
            raise ValueError('inputs/results are not lists')
        return inputs, results

    def get_pairs(self, index: int, one_based: bool = False) -> List[List[Any]]:
        idx = index - 1 if one_based else index
        if idx < 0 or idx >= len(self.rows):
            raise IndexError(f'index {index} out of range (n={len(self.rows)})')
        r = self.rows[idx]
        tests_str = self._extract_tests_str(r)
        if not tests_str:
            raise ValueError('tests field not found or empty')
        inputs, results = self._parse_inputs_results(tests_str)
        n = min(len(inputs), len(results))
        return [[inputs[i], results[i]] for i in range(n)]

    def get_results(self, index: int, one_based: bool = False) -> List[Any]:
        idx = index - 1 if one_based else index
        if idx < 0 or idx >= len(self.rows):
            raise IndexError(f'index {index} out of range (n={len(self.rows)})')
        r = self.rows[idx]
        tests_str = self._extract_tests_str(r)
        if not tests_str:
            raise ValueError('tests field not found or empty')
        _, results = self._parse_inputs_results(tests_str)
        return results


def main() -> None:
    ap = argparse.ArgumentParser(description='Extract (inputs, results) pairs or results list from HumanEval/HumanEval+ item')
    ap.add_argument('-p', '--path', default='HumanEvalPlus.jsonl', help='Path to JSONL(.gz)')
    ap.add_argument('-i', '--index', required=True, type=int, help='Item index (0-based by default)')
    ap.add_argument('--one-based', action='store_true', help='Treat index as 1-based')
    ap.add_argument('--mode', choices=['pairs', 'results'], default='pairs', help='Output pairs or results list')
    ap.add_argument('-o', '--out', default='', help='Output file (default: stdout)')
    args = ap.parse_args()

    if not os.path.exists(args.path):
        print(f'error: file not found: {args.path}', file=sys.stderr)
        sys.exit(2)

    try:
        helper = HumanEvalPairs(args.path)
    except Exception as e:
        print(f'error: {e}', file=sys.stderr)
        sys.exit(2)

    try:
        if args.mode == 'pairs':
            data = helper.get_pairs(args.index, one_based=args.one_based)
        else:
            data = helper.get_results(args.index, one_based=args.one_based)
    except Exception as e:
        print(f'error: {e}', file=sys.stderr)
        sys.exit(2)

    out_text = json.dumps(data, ensure_ascii=False)
    if args.out:
        with open(args.out, 'w', encoding='utf-8') as f:
            f.write(out_text)
    else:
        print(out_text)


if __name__ == '__main__':
    main()

