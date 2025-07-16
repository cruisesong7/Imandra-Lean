# Horn: A Lean Tactic for Real Inequality Proofs

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Lean Version](https://img.shields.io/badge/Lean-4-orange)](https://leanprover.github.io/)

`Horn` is a tactic for the Lean 4 proof assistant that enables the automation of proofs for real number inequalities. It's an "encoder" that transforms a Lean's goal into an S-expression of Horn clauses. This allows the user to offload the proof search to a powerful external solver, Imandra-geo, which returns the Lean proof of the orignial goal. 

## How It Works

The workflow is straightforward:

1.  **State your Goal**: Write your theorem involving real number inequalities in Lean.
2.  **Apply the Tactic**: Use the `horn` tactic on your goal with relevant local hypothesis.
3.  **Generate S-Expression**: The tactic converts your goal into an S-Expression format representing the problem as Horn clauses.
4.  **Solve Externally**: Feed the generated S-Expression to the Imandra-geo solver (link to be updated upon release).
5.  **Integrate Proof**: The solver returns a Lean proof certificate that you can use to close the original goal in Lean.

## Getting Started

### Prerequisites

-   [Lean 4](https://leanprover.github.io/lean4/doc/setup.html)
-   [Lake](https://github.com/leanprover/lake)

### Installation

To add `Horn` to your Lean project, add the following line to your `lakefile.lean`:

```lean
require horn from git "[https://github.com/](https://github.com/)<your-github-username>/horn" @ "main"
```

### Usage

Here is a simple example of how to use the `horn` tactic.

```lean
import RealIneq.Horn 

-- A simple example: The AM-GM inequality for 2 variables
theorem am_gm_2 (x y : ℝ) : 2 * x * y ≤ x^2 + y^2 := by
  -- The `horn` tactic converts this goal into an S-Expression.
  horn
  
  -- The output from `horn` can be sent to the Imandra-geo solver.
  -- The resulting proof certificate is then used to complete the proof.
  sorry -- Placeholder for the integration step.
```

For more detailed examples, please see the `/Examples` directory in this repository.
