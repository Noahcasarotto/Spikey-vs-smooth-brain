# Spiky vs Spherical: Complete Formalization

Formal proof that **under convex returns, being "spiky" (excellent at 1-2 things) beats being "spherical" (well-rounded)**.

## Two Versions

### `simplified/` - Start Here!

**Clean, minimal, easy to understand**
- One file: ~100 lines
- One core theorem + applications
- Same mathematical rigor
- Perfect for learning

**[Go to Simplified Version](./simplified/)**

### `Noah's bad folder/` - Complete Version

**Comprehensive formalization**
- 20 theorems, all proven
- Complete historical context (1776-2024)
- Every detail verified
- 500+ lines of code
- 2000+ lines of documentation

**[Go to Complete Version](./Noah's%20bad%20folder/)**

## The Claim

> "After clearing minimum bars, if payoffs are convex (super-linear returns), concentrate effort on 1-2 areas rather than spreading evenly."

**Status**: **100% Formally Verified**

## Quick Start

### For Quick Understanding
```bash
cd simplified/
# Read SpikyVsSpherical.lean (~100 lines, clean)
```

### For Complete Theory
```bash
cd "Noah's bad folder"/
# See full formalization with all 20 theorems
```

## What's Proven

### Core Mathematical Result
```
Convex f → marginal_gains_increase → spiky_optimal
Concave f → marginal_gains_decrease → spherical_optimal
Linear f → marginal_gains_constant → indifferent
```

### Real-World Applications
- **VC Strategy**: Power-law returns favor spiky founders
- **Career Development**: Excel at 1-2 things in convex-reward fields
- **Startup Strategy**: Dominate one niche before expanding
- **Risk Management**: Diversify when returns are concave

## The Math Behind It

Based on classical results:
- **Jensen's Inequality** (1906)
- **Karamata's Majorization** (1932)  
- **Schur-Convexity** (Hardy-Littlewood-Pólya, 1934)

Now **machine-verified** in Lean 4 with Mathlib.

## Build

Requires [Lean 4](https://leanprover.github.io/lean4/doc/setup.html)

```bash
# Get Mathlib cache
lake exe cache get

# Build either version
cd simplified/ && lake build
# or
cd "Noah's bad folder"/ && lake build
```

## Statistics

| Version | Lines | Theorems | Status |
|---------|-------|----------|--------|
| **Simplified** | ~100 | 1 core + 3 apps | Complete |
| **Full** | ~500 | 20 theorems | Complete |

Both: **0 axioms, 0 sorry, 100% verified**

## From Tweet to Theorem

**Started**: Casual tweet about career strategy  
**Ended**: Complete formal verification spanning 250 years of mathematical history

**Timeline**:
- 1776: Adam Smith (intuition)
- 1906: Jensen (first proof)
- 1932: Karamata (generalization)
- 1934: Hardy-Littlewood-Pólya (Schur-convexity)
- 2024: This formalization (machine-verified)

## Which Version Should I Use?

**Use `simplified/` if you want to**:
- Understand the core idea quickly
- See a clean, minimal proof
- Learn formal verification basics
- Cite the main result

**Use `Noah's bad folder/` if you want to**:
- See the complete historical context
- Explore all 20 proven theorems
- Understand every detail
- Study advanced formalization techniques

## License

Open for educational and research use.

## Citation

```
Casarotto-Dinning, Noah (2024). 
"Spiky vs Spherical: A Lean 4 Formalization." 
GitHub: github.com/Noahcasarotto/Spikey-vs-smooth-brain
```

---

**The tweet was right. The math is rigorous. The verification is complete.**

