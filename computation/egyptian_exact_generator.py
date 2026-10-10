#!/usr/bin/env python3
# Copyright (c) 2026 Yuhang Shi.
# SPDX-License-Identifier: AGPL-3.0-only
"""Exact finite illustration of the candidate construction.

Preregistered run: stages 1..12, at most 60 seconds, Fraction arithmetic.
Permitted command scope: at most 32 stages and at most 60 seconds.
Stop on a failed rational certificate or a time limit. No result from
this finite execution is evidence of novelty or an unrestricted theorem.
The manuscript's termination proof, rather than this run, supplies the
unrestricted mathematical argument.
"""

import argparse
import itertools
import json
import platform
import time
from fractions import Fraction as F
from pathlib import Path


def reciprocal_sum(values):
    return sum((F(1, m) for m in values), F(0))


def prefix_at(j):
    value = j - 1
    return tuple(k + 1 for k in range(value.bit_length()) if value >> k & 1)


def polynomial_stream(tick):
    for height in itertools.count(1):
        for degree in range(height):
            for coefficients in itertools.product(
                range(-height, height + 1), repeat=degree + 1
            ):
                tick()
                if coefficients[-1] and degree + sum(map(abs, coefficients)) == height:
                    yield coefficients


def polynomial_value(coefficients, x):
    value = F(0)
    for coefficient in reversed(coefficients):
        value = value * x + coefficient
    return value


def bad_pair(i):
    a = i * (i + 1)
    d = a + 4
    v = a // 2 + 1
    return F(1, i + 1) + F(1, v), F(1, i) + F(1, d), d, v


def defeat_prefix(a, b, prefix, tick):
    q = reciprocal_sum(prefix)
    if q > a:
        return a, min(b, q), {"branch": "infeasible", "prefix_sum": q}
    c = (a + b) / 2
    values = list(prefix)
    q_now = q
    caps = [b]
    last = values[-1] if values else 0
    while q_now <= a:
        tick()
        reciprocal = 1 / (c - q_now)
        m = max(last + 1, reciprocal.numerator // reciprocal.denominator + 1)
        if m > last + 1:
            caps.append(q_now + F(1, m - 1))
        q_now += F(1, m)
        values.append(m)
        last = m
    upper_cap = min(caps)
    assert a < q_now < c <= upper_cap
    # The manuscript selects the least i. Binary search is equivalent:
    # u_i is strictly decreasing for i >= 3.
    low = max(3, last + 1)
    high = low
    while bad_pair(high)[1] >= upper_cap - q_now:
        tick()
        high *= 2
    while low < high:
        tick()
        middle = (low + high) // 2
        if bad_pair(middle)[1] < upper_cap - q_now:
            high = middle
        else:
            low = middle + 1
    i = low
    r, u, d, v = bad_pair(i)
    assert max(3, last + 1) == i or bad_pair(i - 1)[1] >= upper_cap - q_now
    return q_now + r, q_now + u, {
        "branch": "two_term_improvement",
        "prefix_sum": q,
        "extended_prefix": tuple(values),
        "Q": q_now,
        "B": upper_cap,
        "i": i,
        "D": d,
        "v": v,
        "greedy_tuple": tuple(values) + (i, d + 1),
        "competitor_tuple": tuple(values) + (i + 1, v),
    }


def choose_closed_interval(left, right, coefficients, stage):
    degree = len(coefficients) - 1
    for k in range(1, degree + 2):
        z = left + F(k, degree + 2) * (right - left)
        value = polynomial_value(coefficients, z)
        if value:
            break
    derivative_bound = sum(k * abs(a) for k, a in enumerate(coefficients))
    delta = min(
        (z - left) / 2,
        (right - z) / 2,
        F(1, 2 ** (stage + 1)),
        abs(value) / (2 * (derivative_bound + 1)),
    )
    return z - delta, z + delta, {
        "chosen_k": k,
        "midpoint": z,
        "delta": delta,
        "polynomial_value": value,
        "derivative_bound": derivative_bound,
    }


def verify_stage(previous, prefix, coefficients, stage, open_interval, closed, data):
    """Independent inequalities, without replaying the generation algorithm."""
    a, b = previous
    left, right = open_interval
    lower, upper = closed
    assert a <= left < lower < upper < right <= b
    assert upper - lower <= F(1, 2 ** stage)
    z, delta = (lower + upper) / 2, (upper - lower) / 2
    k_bound = sum(k * abs(v) for k, v in enumerate(coefficients))
    assert polynomial_value(coefficients, z)
    assert k_bound * delta < abs(polynomial_value(coefficients, z)) / 2
    q = reciprocal_sum(prefix)
    if data["branch"] == "infeasible":
        assert right <= q
        return
    greedy = data["greedy_tuple"]
    competitor = data["competitor_tuple"]
    assert greedy[:len(prefix)] == prefix
    assert competitor[:len(prefix)] == prefix
    assert len(greedy) == len(competitor)
    assert all(0 < x < y for x, y in zip(greedy, greedy[1:]))
    assert all(0 < x < y for x, y in zip(competitor, competitor[1:]))
    assert reciprocal_sum(greedy) < reciprocal_sum(competitor) == left
    running = q
    last = prefix[-1] if prefix else 0
    for m in greedy[len(prefix):]:
        # These inequalities certify every greedy choice for all x in (left,right).
        assert running + F(1, m) <= left
        if m > last + 1:
            assert right <= running + F(1, m - 1)
        running += F(1, m)
        last = m


def serialize(value):
    if isinstance(value, F):
        return str(value.numerator) + "/" + str(value.denominator)
    if isinstance(value, dict):
        return {key: serialize(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [serialize(item) for item in value]
    return value


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--stages", type=int, default=12)
    parser.add_argument("--seconds", type=float, default=60)
    parser.add_argument("--output", default="egyptian_exact_certificate.json")
    args = parser.parse_args()
    if not (1 <= args.stages <= 32 and 0 < args.seconds <= 60):
        parser.error("scope must be 1..32 stages and at most 60 seconds")
    start = time.monotonic()
    def tick():
        if time.monotonic() - start > args.seconds:
            raise TimeoutError("preregistered time limit reached")
    polynomials = polynomial_stream(tick)
    interval = (F(1, 4), F(1, 3))
    stages = []
    stop = "scope_complete"
    for stage in range(1, args.stages + 1):
        try:
            tick()
            prefix = prefix_at(stage)
            polynomial = next(polynomials)
            left, right, data = defeat_prefix(*interval, prefix, tick)
            lower, upper, root_data = choose_closed_interval(
                left, right, polynomial, stage
            )
            verify_stage(
                interval, prefix, polynomial, stage,
                (left, right), (lower, upper), data
            )
            stages.append({
                "stage": stage, "prefix": prefix, "polynomial": polynomial,
                "previous_interval": interval, "J": (left, right),
                "I": (lower, upper), "prefix_certificate": data,
                "polynomial_certificate": root_data,
                "independent_exact_inequality_check": True,
            })
            interval = (lower, upper)
        except TimeoutError:
            stop = "time_limit"
            break
    certificate = {
        "construction": "egyptian-explicit-construction-candidate-v1",
        "date_checked": "2026-10-10", "python": platform.python_version(),
        "arithmetic": "exact fractions and unbounded integers",
        "randomness": None, "requested_stages": args.stages,
        "time_limit_seconds": args.seconds, "stop": stop,
        "completed_stages": len(stages),
        "elapsed_seconds": time.monotonic() - start,
        "proof_boundary": "finite illustration only; no novelty claim",
        "stages": stages,
    }
    # The deadline stops construction, but must not prevent saving its certificate.
    Path(args.output).write_text(json.dumps(serialize(certificate), indent=2) + "\n")
    print(json.dumps({
        "completed_stages": len(stages), "stop": stop,
        "elapsed_seconds": certificate["elapsed_seconds"],
        "certificate": str(Path(args.output).resolve()),
        "largest_integer_bits": max(
            max(x.numerator.bit_length(), x.denominator.bit_length())
            for x in interval
        ),
        "all_independent_exact_checks_passed": True,
    }))


if __name__ == "__main__":
    main()
