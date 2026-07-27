/-
  PNP_algorithmic_explicit.lean

  Versión algorítmica del esquema Lean del usuario.

  Idea principal:

  * La prueba original usaba predicados en `Prop`:

        SolvableIn : Problem → PolyLog → Prop
        InP        : Problem → Prop
        InNP       : Problem → Prop

    Eso prueba proposiciones, pero no entrega código ejecutable.

  * Aquí reemplazamos esas proposiciones por paquetes en `Type` que contienen
    funciones ejecutables:

        Decider.run : L.Input → Bool

    junto con pruebas de corrección, que Lean puede borrar en runtime.

  Este archivo compila sin `sorry` y sin `axiom`. No prueba P = NP real:
  muestra qué datos algorítmicos habría que proporcionar para que la conclusión
  devuelva un algoritmo explícito.
-/

namespace PNPAlgorithmicExplicit

/-! ## Complejidades polilogarítmicas -/

/-- Un orden polilogarítmico `O((log n)^k)`, representado por el exponente `k`. -/
structure PolyLog where
  exp : Nat
deriving Repr, DecidableEq

/-- Anidar dos procedimientos polilogarítmicos suma exponentes. -/
def PolyLog.nest (a b : PolyLog) : PolyLog := ⟨a.exp + b.exp⟩

/-- `O(log n)`. -/
def logn : PolyLog := ⟨1⟩

/-- `O(log² n)`. -/
def log2n : PolyLog := ⟨2⟩

/-- `O(log n) · O(log n) = O(log² n)`. -/
theorem nesting_two_logs : PolyLog.nest logn logn = log2n := rfl

/-! ## Problemas de decisión y decidores ejecutables -/

/-- Un problema de decisión: tipo de entradas y predicado semántico de aceptación. -/
structure Problem where
  Input : Type
  yes : Input → Prop

/--
Un algoritmo ejecutable para decidir un problema.

`run` es el programa real. `correct` es la prueba de corrección.
- espectáculo importante: `run` vive en `Type` y se ejecuta;
- `correct` vive en `Prop` y Lean puede borrarlo al compilar.
-/
structure Decider (L : Problem) where
  run : L.Input → Bool
  correct : ∀ x, run x = true ↔ L.yes x

/-- Un decidor con una cota temporal polilogarítmica. -/
structure TimedDecider (L : Problem) (b : PolyLog) where
  decider : Decider L
  timeBound : True
  -- En una formalización real, `True` se reemplazaría por una definición
  -- precisa de coste temporal, por ejemplo: `TimeBound decider.run b`.

/-- Datos algorítmicos de que `L ∈ P`: decidor + prueba de tiempo polinomial. -/
structure InPAlg (L : Problem) where
  decider : Decider L
  polynomialTime : True
  -- En una formalización real: `PolynomialTime decider.run`.

/-! ## Reducciones ejecutables -/

/-- Reducción computable de un problema `A` a un problema `B`. -/
structure Reduction (A B : Problem) where
  map : A.Input → B.Input
  correct : ∀ x, B.yes (map x) ↔ A.yes x
  polyTime : True

/-- Transporta un decidor de `B` a un decidor de `A` mediante una reducción `A ≤ B`. -/
def Decider.viaReduction {A B : Problem}
    (db : Decider B) (r : Reduction A B) : Decider A where
  run := fun x => db.run (r.map x)
  correct := by
    intro x
    exact Iff.trans (db.correct (r.map x)) (r.correct x)

/-- Si `B ∈ P` y `A ≤p B`, entonces `A ∈ P`, con algoritmo explícito. -/
def InPAlg.viaReduction {A B : Problem}
    (hb : InPAlg B) (r : Reduction A B) : InPAlg A where
  decider := Decider.viaReduction hb.decider r
  polynomialTime := trivial

/-- Datos algorítmicos de que `L ∈ NP`: aquí lo modelamos como reducción explícita a SAT. -/
structure InNPAlg (L SAT : Problem) where
  reduceToSAT : Reduction L SAT

/-! ## Procedimiento externo de búsqueda→decisión con oráculo -/

/--
Un procedimiento con oráculo.

Piensa en `run oracle x` como el bucle de búsqueda→decisión: hace consultas al
oráculo `oracle` y luego produce la respuesta para `x`.

La prueba `correct` dice: si el oráculo es correcto, entonces el procedimiento
completo es correcto.
-/
structure TimedOracleProcedure (L : Problem) (outerCost : PolyLog) where
  run : (L.Input → Bool) → L.Input → Bool
  correct :
    ∀ oracle : L.Input → Bool,
      (∀ x, oracle x = true ↔ L.yes x) →
      ∀ x, run oracle x = true ↔ L.yes x
  timeBound : True
  -- En una formalización real: número de consultas, coste overhead, etc.

/--
Anidamiento algorítmico explícito:
si el procedimiento externo cuesta `outerCost` y cada llamada al oráculo cuesta
`innerCost`, el algoritmo compuesto cuesta `outerCost.nest innerCost`.
-/
def TimedOracleProcedure.instantiate {L : Problem} {outerCost innerCost : PolyLog}
    (proc : TimedOracleProcedure L outerCost)
    (oracleSolver : TimedDecider L innerCost) :
    TimedDecider L (PolyLog.nest outerCost innerCost) where
  decider := {
    run := fun x => proc.run oracleSolver.decider.run x
    correct := by
      intro x
      exact proc.correct oracleSolver.decider.run oracleSolver.decider.correct x
  }
  timeBound := trivial

/-! ## Versión algorítmica del paquete del paper -/

structure PaperAlg where
  /-- SAT como problema de decisión formalizado. -/
  SAT : Problem

  /-- Orden de verificación holográfica/PCP. -/
  pcpOrder : PolyLog
  pcp_is_logn : pcpOrder = logn

  /-- Algoritmo/verificador usado como oráculo de decisión para SAT. -/
  pcpSolver : TimedDecider SAT pcpOrder

  /-- Orden del procedimiento búsqueda→decisión. -/
  searchOrder : PolyLog
  search_is_logn : searchOrder = logn

  /-- Procedimiento externo que usa el oráculo anterior. -/
  searchToDecision : TimedOracleProcedure SAT searchOrder

  /-- La inclusión algorítmica `POLYLOGTIME ⊂ P`. -/
  polylog_subset_P : ∀ L b, TimedDecider L b → InPAlg L

namespace PaperAlg

variable (P : PaperAlg)

/-- Complejidad total: `O(log n) · O(log n) = O(log² n)`. -/
theorem total_complexity :
    PolyLog.nest P.searchOrder P.pcpOrder = log2n := by
  rw [P.search_is_logn, P.pcp_is_logn]
  rfl

/-- Algoritmo SAT anidando explícitamente búsqueda→decisión con el oráculo PCP. -/
def sat_solver_nested : TimedDecider P.SAT (PolyLog.nest P.searchOrder P.pcpOrder) :=
  P.searchToDecision.instantiate P.pcpSolver

/-- El mismo algoritmo, reindexado con la cota `O(log² n)`. -/
def sat_solver_log2n : TimedDecider P.SAT log2n := by
  rw [← total_complexity P]
  exact sat_solver_nested P

/-- SAT está en P, pero ahora con un decidor ejecutable guardado dentro del paquete. -/
def sat_in_P_alg : InPAlg P.SAT :=
  P.polylog_subset_P P.SAT log2n (sat_solver_log2n P)

/-- ESTE es el algoritmo explícito para SAT. -/
def sat_algorithm : P.SAT.Input → Bool :=
  (sat_in_P_alg P).decider.run

/-- Corrección del algoritmo explícito para SAT. -/
theorem sat_algorithm_correct (x : P.SAT.Input) :
    sat_algorithm P x = true ↔ P.SAT.yes x :=
  (sat_in_P_alg P).decider.correct x

/--
Forma algorítmica de la conclusión tipo `P = NP`:
para todo problema `L` equipado con una reducción explícita a SAT,
construimos datos explícitos de que `L ∈ P`.
-/
def p_eq_np_algorithmic (L : Problem) (hL : InNPAlg L P.SAT) : InPAlg L :=
  InPAlg.viaReduction (sat_in_P_alg P) hL.reduceToSAT

/-- Algoritmo explícito producido para un problema `L ∈ NP`. -/
def np_algorithm (L : Problem) (hL : InNPAlg L P.SAT) : L.Input → Bool :=
  (p_eq_np_algorithmic P L hL).decider.run

/-- Corrección del algoritmo producido para `L`. -/
theorem np_algorithm_correct (L : Problem) (hL : InNPAlg L P.SAT) (x : L.Input) :
    np_algorithm P L hL x = true ↔ L.yes x :=
  (p_eq_np_algorithmic P L hL).decider.correct x

end PaperAlg

/-! ## Instancia de juguete ejecutable para demostrar `#eval` -/

/-- Problema juguete: decidir si un natural es par. -/
abbrev EvenProblem : Problem where
  Input := Nat
  yes := fun n : Nat => n % 2 = 0

/-- Decidor ejecutable para `EvenProblem`. -/
def evenDecider : Decider EvenProblem where
  run := fun n : Nat => decide (n % 2 = 0)
  correct := by
    intro n
    change decide ((n : Nat) % 2 = 0) = true ↔ (n : Nat) % 2 = 0
    by_cases h : (n : Nat) % 2 = 0
    · simp [h]
    · simp [h]

/-- Decidor `O(log n)` de juguete. -/
def evenTimedDecider : TimedDecider EvenProblem logn where
  decider := evenDecider
  timeBound := trivial

/-- Procedimiento externo de juguete: simplemente llama al oráculo una vez. -/
def identityOracleProcedure : TimedOracleProcedure EvenProblem logn where
  run := fun oracle x => oracle x
  correct := by
    intro oracle oracle_correct x
    exact oracle_correct x
  timeBound := trivial

/-- Paquete algorítmico de juguete. -/
def ToyPaper : PaperAlg where
  SAT := EvenProblem
  pcpOrder := logn
  pcp_is_logn := rfl
  pcpSolver := evenTimedDecider
  searchOrder := logn
  search_is_logn := rfl
  searchToDecision := identityOracleProcedure
  polylog_subset_P := fun _L _b solver =>
    { decider := solver.decider, polynomialTime := trivial }

/-- Otro problema de juguete: decidir si `n + 1` es par. -/
abbrev ShiftEvenProblem : Problem where
  Input := Nat
  yes := fun n : Nat => (n + 1) % 2 = 0

/-- Reducción explícita de `ShiftEvenProblem` a `EvenProblem`. -/
def ShiftEven_to_Even : Reduction ShiftEvenProblem EvenProblem where
  map := fun n : Nat => n + 1
  correct := by
    intro n
    rfl
  polyTime := trivial

/-- Datos algorítmicos de que `ShiftEvenProblem ∈ NP` relativo al SAT de juguete. -/
def ShiftEven_InNP : InNPAlg ShiftEvenProblem ToyPaper.SAT where
  reduceToSAT := ShiftEven_to_Even

#eval (PolyLog.nest logn logn).exp                         -- 2
#eval decide (PolyLog.nest logn logn = log2n)               -- true

-- Ejecutar el algoritmo SAT producido por el paquete algorítmico:
#eval PaperAlg.sat_algorithm ToyPaper (4 : Nat)             -- true
#eval PaperAlg.sat_algorithm ToyPaper (5 : Nat)             -- false

-- Ejecutar el algoritmo producido para otro problema vía reducción a SAT:
#eval PaperAlg.np_algorithm ToyPaper ShiftEvenProblem ShiftEven_InNP (3 : Nat) -- true
#eval PaperAlg.np_algorithm ToyPaper ShiftEvenProblem ShiftEven_InNP (4 : Nat) -- false

#check PaperAlg.sat_algorithm
#check PaperAlg.p_eq_np_algorithmic
#print axioms PaperAlg.p_eq_np_algorithmic

end PNPAlgorithmicExplicit
