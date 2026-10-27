import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Map and Governor: χ counts the boundary's full turns (Descartes / discrete Gauss–Bonnet)

Model the defect boundary as a closed triangulated surface: `F` triangles, each with three
corners at vertices, corner angles summing to `π` per triangle, and every edge shared by two
triangles (`3F = 2E`). The angle defect at a vertex is `2π` minus the angles meeting there.

`descartes`: the total defect is `2π (V − E + F) = 2π χ`, for any triangulation and any angles.

So `χ` is the number of full `2π` turns the boundary must make to close — a count of
closures, independent of shape, size and triangulation. Map's term is that count with unit
weight (one transition per closure), and Governor distributes the same total over the cycle.
-/

namespace PMArch.Descartes
open Finset Real

/-- A closed triangulated surface with corner angles. -/
structure Triangulation (V F : ℕ) where
  /-- vertex of corner `j` of triangle `f` -/
  corner : Fin F → Fin 3 → Fin V
  /-- angle at that corner -/
  angle : Fin F → Fin 3 → ℝ
  /-- each triangle's angles sum to `π` -/
  triangle_sum : ∀ f, ∑ j, angle f j = π

/-- Angle defect at a vertex. -/
noncomputable def defect {V F : ℕ} (T : Triangulation V F) (v : Fin V) : ℝ :=
  2 * π - ∑ c ∈ (univ.filter fun c : Fin F × Fin 3 => T.corner c.1 c.2 = v), T.angle c.1 c.2

/-- **Descartes' theorem.** Total angle defect equals `2π χ`. -/
theorem descartes {V F E : ℕ} (T : Triangulation V F) (hE : 3 * F = 2 * E) :
    ∑ v, defect T v = 2 * π * ((V : ℝ) - E + F) := by
  have hcorners : ∑ v : Fin V, ∑ c ∈ (univ.filter fun c : Fin F × Fin 3 => T.corner c.1 c.2 = v),
      T.angle c.1 c.2 = ∑ c : Fin F × Fin 3, T.angle c.1 c.2 :=
    Finset.sum_fiberwise univ (fun c : Fin F × Fin 3 => T.corner c.1 c.2) _
  have htotal : ∑ c : Fin F × Fin 3, T.angle c.1 c.2 = F * π := by
    rw [Fintype.sum_prod_type]
    simp [T.triangle_sum]
  have hE' : (E : ℝ) = 3 * F / 2 := by
    have : ((3 * F : ℕ) : ℝ) = ((2 * E : ℕ) : ℝ) := by rw [hE]
    push_cast at this; linarith
  unfold defect
  rw [Finset.sum_sub_distrib, hcorners, htotal]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hE']; ring

/-- The sphere (χ = 2): total turning `4π`, two full turns, whatever the triangulation. -/
theorem sphere_two_turns {V F E : ℕ} (T : Triangulation V F) (hE : 3 * F = 2 * E)
    (hχ : (V : ℝ) - E + F = 2) : (∑ v, defect T v) / (2 * π) = 2 := by
  rw [descartes T hE, hχ]; field_simp [pi_ne_zero]

/-- A witness: the tetrahedron (V = 4, E = 6, F = 4), equilateral angles. -/
noncomputable def tetrahedron : Triangulation 4 4 where
  corner := ![![1, 2, 3], ![0, 2, 3], ![0, 1, 3], ![0, 1, 2]]
  angle := fun _ _ => π / 3
  triangle_sum := fun _ => by simp; ring

theorem tetrahedron_turns : (∑ v, defect tetrahedron v) / (2 * π) = 2 :=
  sphere_two_turns tetrahedron (E := 6) (by norm_num) (by norm_num)

end PMArch.Descartes
