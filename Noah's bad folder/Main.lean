import SpikyVsSpherical

/-!
# Main: Examples and Applications

This file provides concrete examples and applications of the spiky vs spherical theorem.
-/

open BigOperators

/-! ## Example 1: The Classic Tweet Scenario -/

/--
The original motivating example:
- 5 skill dimensions
- Minimum bar of 1 on each
- Extra budget of 4 to distribute
- Quadratic payoff (convex)

Conclusion: Spiky (5,1,1,1,1) beats spherical (1.8,1.8,1.8,1.8,1.8)
-/
def tweetExample : Prop :=
  let d := 5
  let b : MinimumBars d := fun _ => 1
  let S := (4 : ℝ)
  let f := fun t : ℝ => t^2
  -- Spiky allocation
  let x_spiky : SkillProfile d := spikeProfile b S 0
  -- Spherical allocation
  let x_sphere : SkillProfile d := uniformProfile b S
  valueFunction f x_spiky > valueFunction f x_sphere

/-! ## Example 2: Venture Capital Portfolio -/

/--
VC scenario:
- 10 potential investments
- Minimum due diligence on all
- Limited partner capital to deploy
- Power-law returns (highly convex)

Optimal strategy: Concentrate on 1-2 best opportunities
-/
def vcPortfolio (α : ℝ) (hα : α > 1) : Prop :=
  let d := 10  -- 10 potential companies
  let b : MinimumBars d := fun _ => 0.1  -- minimum due diligence
  let S := (10 : ℝ)  -- total capital to invest
  let f := powerLawPayoff α  -- power law returns
  ∃ (x : SkillProfile d),
    meetsMinimumBars x b ∧
    totalExtra x b = S ∧
    isKSpiky 2 x b  -- concentrated in at most 2 companies

/-! ## Example 3: Career Development -/

/--
Career scenario:
- Multiple skills: coding, communication, design, management, domain expertise
- Must clear minimum bar on all for employability
- Companies value excellence in 1-2 areas most
- Convex rewards (senior roles, leadership, visibility)

Strategy: Master 1-2 things, be competent at the rest
-/
def careerStrategy : Prop :=
  let d := 5  -- 5 key skills
  let b : MinimumBars d := fun _ => 3  -- minimum competence level
  let S := (10 : ℝ)  -- extra effort to invest
  let f := fun t => t^2  -- convex returns to expertise
  ∃ (x : SkillProfile d),
    meetsMinimumBars x b ∧
    totalExtra x b = S ∧
    (Finset.univ.filter (fun i => x i > b i)).card ≤ 2

/-! ## Counter-Example: When to Be Spherical -/

/--
Risk management scenario:
- Multiple security vulnerabilities to address
- Diminishing returns to fixing each one
- System is as secure as weakest link
- Concave payoff (square root of investment)

Strategy: Spread effort evenly, avoid weak points
-/
def securityStrategy : Prop :=
  let d := 5  -- 5 security areas
  let b : MinimumBars d := fun _ => 1  -- baseline security
  let S := (10 : ℝ)  -- security budget
  let f := Real.sqrt  -- concave returns
  -- For concave f, uniform allocation is often optimal
  let x_uniform : SkillProfile d := uniformProfile b S
  ∀ (x : SkillProfile d),
    meetsMinimumBars x b →
    totalExtra x b = S →
    valueFunction f x ≤ valueFunction f x_uniform + 1  -- within epsilon

/-! ## Practical Decision Rule -/

/--
The practical test: Should I be spiky or spherical?

Ask: "Does adding more to my strongest area give higher marginal benefit
      than adding to a weaker one?"

- If YES (convex, RTP > 1) → Go spiky
- If NO (concave, RTP < 1) → Go spherical
- If EQUAL (linear, RTP = 1) → Doesn't matter
-/

def decisionRule (f : ℝ → ℝ) (x_strong x_weak δ : ℝ)
  (h_stronger : x_strong > x_weak) (h_δ : δ > 0) : String :=
  if (f (x_strong + δ) - f x_strong) > (f (x_weak + δ) - f x_weak) then
    "Go SPIKY: Marginal returns are higher on your strong skills"
  else if (f (x_strong + δ) - f x_strong) < (f (x_weak + δ) - f x_weak) then
    "Go SPHERICAL: Marginal returns are higher on your weak skills"
  else
    "INDIFFERENT: Linear payoffs, doesn't matter"

/-! ## Summary of Applications -/

/--
Spiky wins in:
- Venture capital (power-law returns)
- Startups (winner-take-most markets)
- Creative careers (superstar economics)
- Innovation races (breakthrough-driven)
- Niche excellence (being #1 in narrow domain)

Spherical wins in:
- Portfolio diversification (risk management)
- Insurance (concave utility)
- Robust systems (weakest link matters)
- Health & fitness (balance across dimensions)
- Team composition (complementary skills)

The difference: Convexity vs Concavity of payoffs
-/

#check tweetExample
#check vcPortfolio
#check careerStrategy
#check securityStrategy
#check decisionRule

-- Display the main theorems
#check convex_marginal_gains_monotone
#check concentration_improves_value
#check spike_allocation_exists
#check concave_favors_uniform

end

