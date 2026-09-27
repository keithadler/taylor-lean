import Lean
open Lean Widget

/-!
# What the gradient is doing

A Taylor expansion says that near a point `θ`, a smooth loss looks like its value, plus the gradient
dotted with the step, plus half the step's quadratic form under the Hessian, plus terms that shrink
faster still:

  `L(θ + Δ) = L(θ) + ∇L(θ)ᵀΔ + ½ ΔᵀH(θ)Δ + …`

This file takes one loss surface in two parameters and proves that, exactly, over the rationals,
with core Lean and nothing else. For a polynomial loss the expansion is not an approximation at
all: the "…" is a short explicit remainder, and every statement below is an identity. Then it
proves what the pictures in every optimization course are trying to show: the gradient is the slope
the difference quotient settles on, halving a step cuts the first-order error by four and the
second-order error by eight, and a small step against the gradient goes downhill.

Put the cursor on `#widget` at the bottom and open the Infoview to play with it: drag the point,
change the step, rotate the surface.
-/

namespace Taylor

/-! ## The loss surface -/

/-- The loss: a bowl in `(x, y) = (θ₁, θ₂)`, steeper on the right, with a tilt from the `x·y` term. -/
def L (x y : Rat) : Rat := x ^ 4 / 16 + x ^ 2 / 2 + x / 2 + y ^ 2 / 2 + x * y / 4 + 1 / 2

/-- `∂L/∂x`. -/
def Lx (x y : Rat) : Rat := x ^ 3 / 4 + x + 1 / 2 + y / 4
/-- `∂L/∂y`. -/
def Ly (x y : Rat) : Rat := y + x / 4

/-- The Hessian entries `∂²L/∂x²`, `∂²L/∂x∂y`, `∂²L/∂y²`. -/
def Lxx (x _y : Rat) : Rat := 3 * x ^ 2 / 4 + 1
def Lxy (_x _y : Rat) : Rat := 1 / 4
def Lyy (_x _y : Rat) : Rat := 1

/-- The first-order model at `(x, y)`, evaluated at the step `(a, b)`: the tangent plane. -/
def first (x y a b : Rat) : Rat := L x y + (Lx x y * a + Ly x y * b)

/-- The second-order model: the tangent plane plus half the Hessian's quadratic form. -/
def second (x y a b : Rat) : Rat :=
  first x y a b + (Lxx x y * a ^ 2 + 2 * Lxy x y * a * b + Lyy x y * b ^ 2) / 2

/-! ## The expansion is exact -/

/-- Taylor's theorem for this loss, with nothing hidden: after the second-order model, what is left
is the third-order term `(1/6)·∂³L/∂x³·a³ = x a³ / 4` and the fourth-order term `a⁴ / 16`. -/
theorem taylor (x y a b : Rat) :
    L (x + a) (y + b) = second x y a b + x * a ^ 3 / 4 + a ^ 4 / 16 := by
  unfold second first; unfold L Lx Ly Lxx Lxy Lyy; grind

/-- What the first-order model misses is exactly the quadratic form, plus the small remainder. -/
theorem first_order_error (x y a b : Rat) :
    L (x + a) (y + b) - first x y a b
      = (Lxx x y * a ^ 2 + 2 * Lxy x y * a * b + Lyy x y * b ^ 2) / 2 + x * a ^ 3 / 4 + a ^ 4 / 16 := by
  unfold first; unfold L Lx Ly Lxx Lxy Lyy; grind

/-- What the second-order model misses is cubic in the step. -/
theorem second_order_error (x y a b : Rat) :
    L (x + a) (y + b) - second x y a b = a ^ 3 * (x / 4 + a / 16) := by
  have := taylor x y a b; grind

/-! ## The gradient is the slope

Take a direction `(a, b)` and a step `h ≠ 0`. The difference quotient `(L(θ + hΔ) − L(θ)) / h` is the
gradient dotted with the direction, plus `h` times something that stays bounded as `h` shrinks. So as
`h → 0` the quotient settles on `∇L(θ)ᵀΔ`: that number is what the gradient is. -/

theorem slope (x y a b h : Rat) (hh : h ≠ 0) :
    (L (x + h * a) (y + h * b) - L x y) / h
      = (Lx x y * a + Ly x y * b)
        + h * ((Lxx x y * a ^ 2 + 2 * Lxy x y * a * b + Lyy x y * b ^ 2) / 2
               + h * (x * a ^ 3 / 4) + h ^ 2 * (a ^ 4 / 16)) := by
  unfold L Lx Ly Lxx Lxy Lyy; grind

/-! ## Why smaller steps are safer

Scale a step by `h`. The first-order error is `h²` times the quadratic form plus higher powers, and the
second-order error starts at `h³`. Halving the step divides the first by about four and the second by
about eight. -/

theorem first_order_error_scales (x y a b h : Rat) :
    L (x + h * a) (y + h * b) - first x y (h * a) (h * b)
      = h ^ 2 * ((Lxx x y * a ^ 2 + 2 * Lxy x y * a * b + Lyy x y * b ^ 2) / 2)
        + h ^ 3 * (x * a ^ 3 / 4) + h ^ 4 * (a ^ 4 / 16) := by
  unfold first; unfold L Lx Ly Lxx Lxy Lyy; grind

theorem second_order_error_scales (x y a b h : Rat) :
    L (x + h * a) (y + h * b) - second x y (h * a) (h * b)
      = h ^ 3 * (x * a ^ 3 / 4) + h ^ 4 * (a ^ 4 / 16) := by
  have := second_order_error x y (h * a) (h * b); grind

/-! ## Gradient descent goes downhill

Step against the gradient, `Δ = −η ∇L(θ)`. The loss changes by `−η ‖∇L(θ)‖²` to first order, which is
negative whenever the gradient is not zero; the corrections start at `η²`. -/

theorem descent (x y η : Rat) :
    let gx := Lx x y; let gy := Ly x y
    L (x - η * gx) (y - η * gy)
      = L x y - η * (gx ^ 2 + gy ^ 2)
        + η ^ 2 * ((Lxx x y * gx ^ 2 + 2 * Lxy x y * gx * gy + Lyy x y * gy ^ 2) / 2)
        - η ^ 3 * (x * gx ^ 3 / 4) + η ^ 4 * (gx ^ 4 / 16) := by
  intro gx gy
  unfold gx gy L Lx Ly Lxx Lxy Lyy; grind

/-! ## The picture, computed

The widget's starting point is `θ = (3/5, 0)` with the step direction `(1, 1/2)`. Everything it
prints in its table is computed here, by Lean, from the definitions above. -/

def θ₀ : Rat × Rat := (3 / 5, 0)
def dir : Rat × Rat := (1, 1 / 2)

/-- One row of the table: the step scale `h`, the true loss, both models, and both errors. -/
def row (h : Rat) : Rat × Rat × Rat × Rat × Rat × Rat :=
  let (x, y) := θ₀; let a := h * dir.1; let b := h * dir.2
  let t := L (x + a) (y + b)
  (h, t, first x y a b, second x y a b, t - first x y a b, t - second x y a b)

def steps : List Rat := [1, 1 / 2, 1 / 4, 1 / 8, 1 / 16]

/-- At the widget's point, halving the step from `1/8` to `1/16` divides the first-order error by more
than 3.9 and the second-order error by more than 7.8, checked by Lean's kernel on the exact rationals. -/
theorem halving_at_the_picture :
    let e1 := fun h => (row h).2.2.2.2.1
    let e2 := fun h => (row h).2.2.2.2.2
    e1 (1 / 8) > 39 / 10 * e1 (1 / 16) ∧ e2 (1 / 8) > 78 / 10 * e2 (1 / 16) := by
  decide +kernel

/-- One gradient step of size `η = 1/10` from the widget's point lowers the loss. -/
theorem one_step_downhill :
    let (x, y) := θ₀
    L (x - 1 / 10 * Lx x y) (y - 1 / 10 * Ly x y) < L x y := by
  decide +kernel

/-! ## The widget -/

/-- The loss as a list of monomials `c · xⁱ · yʲ`, which is what the widget draws. -/
def terms : List (Rat × Nat × Nat) :=
  [(1 / 16, 4, 0), (1 / 2, 2, 0), (1 / 2, 1, 0), (1 / 2, 0, 2), (1 / 4, 1, 1), (1 / 2, 0, 0)]

def evalTerms (ts : List (Rat × Nat × Nat)) (x y : Rat) : Rat :=
  ts.foldr (fun (c, i, j) acc => c * x ^ i * y ^ j + acc) 0

/-- The widget draws exactly `L`: the monomial list it receives is the same function. -/
theorem terms_eq_L (x y : Rat) : evalTerms terms x y = L x y := by
  simp only [evalTerms, terms, List.foldr, L]; grind

private def ratJson (r : Rat) : Json := Json.arr #[toJson r.num, toJson r.den]

def widgetProps : Json :=
  let r := fun (q : Rat) => ratJson q
  Json.mkObj [
    ("terms", Json.arr (terms.map fun (c, i, j) => Json.arr #[r c, toJson i, toJson j]).toArray),
    ("theta", Json.arr #[r θ₀.1, r θ₀.2]),
    ("dir", Json.arr #[r dir.1, r dir.2]),
    ("table", Json.arr (steps.map fun h =>
      let (h, t, f, s, e1, e2) := row h
      Json.arr #[r h, r t, r f, r s, r e1, r e2]).toArray)]

@[widget_module]
def TaylorWidget : Widget.Module where
  javascript := include_str "widget" / "Taylor.js"

end Taylor

open Taylor in
#widget TaylorWidget with widgetProps
