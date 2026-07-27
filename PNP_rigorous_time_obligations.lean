/-
  PNP_rigorous_time_obligations.lean

  Refactor riguroso del modelo de tiempo:
  * No hay `structure Paper`.
  * No hay `timeBound : True`.
  * `TimedDecider` lleva una función explícita de pasos.
  * SAT tiene una medida de tamaño `Formula.size`.
  * La reducción búsqueda→decisión bit-a-bit se modela con un contador real
    de consultas: `Formula.varBound`.
  * El archivo compila sin `sorry` y sin `axiom`.

  Este archivo NO cierra `p_eq_np`: deja visibles como proposiciones los
  ingredientes exactos que habría que formalizar para poder cerrarlo.
-/

namespace PNPRigorousTime

/-! ## Órdenes polilogarítmicos -/

structure PolyLog where
  exp : Nat
deriving Repr, DecidableEq

def PolyLog.nest (a b : PolyLog) : PolyLog := ⟨a.exp + b.exp⟩

def logn : PolyLog := ⟨1⟩
def log2n : PolyLog := ⟨2⟩

theorem nesting_two_logs : PolyLog.nest logn logn = log2n := rfl

/-! ## Fórmulas SAT y tamaño -/

inductive Formula where
  | var : Nat → Formula
  | top : Formula
  | bot : Formula
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
deriving Repr, DecidableEq

abbrev Assignment := Nat → Bool

namespace Formula

/-- Tamaño sintáctico. Para variables incluye el índice, así `varBound ≤ size`. -/
def size : Formula → Nat
  | var n => n + 1
  | top => 1
  | bot => 1
  | neg φ => size φ + 1
  | conj φ ψ => size φ + size ψ + 1
  | disj φ ψ => size φ + size ψ + 1

/-- Cota superior del número de variables relevantes. -/
def varBound : Formula → Nat
  | var n => n + 1
  | top => 0
  | bot => 0
  | neg φ => varBound φ
  | conj φ ψ => Nat.max (varBound φ) (varBound ψ)
  | disj φ ψ => Nat.max (varBound φ) (varBound ψ)

/-- Evaluación bajo asignación. -/
def eval (σ : Assignment) : Formula → Bool
  | var n => σ n
  | top => true
  | bot => false
  | neg φ => !(eval σ φ)
  | conj φ ψ => eval σ φ && eval σ ψ
  | disj φ ψ => eval σ φ || eval σ ψ

/-- Sustitución de una variable por una constante booleana. -/
def substVar (v : Nat) (value : Bool) : Formula → Formula
  | var n => if n = v then (if value then top else bot) else var n
  | top => top
  | bot => bot
  | neg φ => neg (substVar v value φ)
  | conj φ ψ => conj (substVar v value φ) (substVar v value ψ)
  | disj φ ψ => disj (substVar v value φ) (substVar v value ψ)

/-- Lema básico: el número de variables está acotado por el tamaño sintáctico. -/
theorem varBound_le_size : ∀ φ : Formula, varBound φ ≤ size φ := by
  intro φ
  induction φ with
  | var n => simp [varBound, size]
  | top => simp [varBound, size]
  | bot => simp [varBound, size]
  | neg φ ih =>
      simp [varBound, size]
      omega
  | conj φ ψ ihφ ihψ =>
      simp [varBound, size]
      exact (Nat.max_le).2 ⟨by omega, by omega⟩
  | disj φ ψ ihφ ihψ =>
      simp [varBound, size]
      exact (Nat.max_le).2 ⟨by omega, by omega⟩

end Formula

/-! ## Problemas, decidores y cotas no triviales -/

structure Problem where
  Input : Type
  yes : Input → Prop
  size : Input → Nat

/-- SAT como problema de decisión. La semántica aquí es abstracta por decidibilidad booleana. -/
def getBit : List Bool → Nat → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: bs, n + 1 => getBit bs n

def assignmentFromBits (bits : List Bool) : Assignment :=
  fun i => getBit bits i

def allBitVectors : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
      let xs := allBitVectors n
      (xs.map (fun bs => false :: bs)) ++ (xs.map (fun bs => true :: bs))

/-- Decisor semántico por enumeración. Se mantiene separado del modelo PCP. -/
def satBoolBruteforce (φ : Formula) : Bool :=
  (allBitVectors φ.varBound).any
    (fun bits => Formula.eval (assignmentFromBits bits) φ)

abbrev SAT : Problem where
  Input := Formula
  yes := fun φ => satBoolBruteforce φ = true
  size := Formula.size

structure Decider (L : Problem) where
  run : L.Input → Bool
  correct : ∀ x, run x = true ↔ L.yes x

/-- Cota polilogarítmica explícita sobre una función de pasos. -/
def IsPolyLogBounded {α : Type}
    (size : α → Nat) (steps : α → Nat) (b : PolyLog) : Prop :=
  ∃ C : Nat, ∀ x : α,
    steps x ≤ C * ((Nat.log2 (size x + 1)) ^ b.exp + 1)

/-- Cota polinomial explícita sobre una función de pasos. -/
def IsPolynomialBounded {α : Type}
    (size : α → Nat) (steps : α → Nat) (degree : Nat) : Prop :=
  ∃ C : Nat, ∀ x : α,
    steps x ≤ C * ((size x + 1) ^ degree + 1)

/-- Decidor con función explícita de pasos. -/
structure TimedDecider (L : Problem) (b : PolyLog) where
  decider : Decider L
  steps : L.Input → Nat
  timeBound : IsPolyLogBounded L.size steps b

/-- Decidor polinomial con función explícita de pasos. -/
structure InPAlg (L : Problem) where
  decider : Decider L
  steps : L.Input → Nat
  degree : Nat
  timeBound : IsPolynomialBounded L.size steps degree

/-- `POLYLOGTIME ⊂ P`, probado con `Nat.log2_le_self`. -/
def polylog_subset_P_alg (L : Problem) (b : PolyLog)
    (h : TimedDecider L b) : InPAlg L where
  decider := h.decider
  steps := h.steps
  degree := b.exp
  timeBound := by
    rcases h.timeBound with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x
    have h₁ : Nat.log2 (L.size x + 1) ≤ L.size x + 1 :=
      Nat.log2_le_self (L.size x + 1)
    have h₂ : (Nat.log2 (L.size x + 1)) ^ b.exp ≤ (L.size x + 1) ^ b.exp :=
      Nat.pow_le_pow_left h₁ b.exp
    have h₃ :
        (Nat.log2 (L.size x + 1)) ^ b.exp + 1 ≤
          (L.size x + 1) ^ b.exp + 1 :=
      Nat.add_le_add_right h₂ 1
    exact Nat.le_trans (hC x) (Nat.mul_le_mul_left C h₃)

/-! ## Search-to-decision bit-a-bit, sin esconder consultas -/

/-- Resultado de una búsqueda: asignación parcial como lista de bits. -/
def searchAssignmentAux
    (oracle : Formula → Bool) : Nat → Nat → Formula → List Bool
  | 0, _, _ => []
  | k + 1, i, φ =>
      let φ0 := Formula.substVar i false φ
      if oracle φ0 then
        false :: searchAssignmentAux oracle k (i + 1) φ0
      else
        let φ1 := Formula.substVar i true φ
        true :: searchAssignmentAux oracle k (i + 1) φ1

/-- Bucle explícito que intenta fijar variables una por una. -/
def searchAssignment (oracle : Formula → Bool) (φ : Formula) : List Bool :=
  searchAssignmentAux oracle φ.varBound 0 φ

/-- Número real de consultas del procedimiento bit-a-bit. -/
def searchToDecisionQueries (φ : Formula) : Nat :=
  φ.varBound

/-- El contador de consultas es exactamente la cota de variables. -/
theorem searchToDecisionQueries_exact (φ : Formula) :
    searchToDecisionQueries φ = φ.varBound := rfl

/-- El bucle bit-a-bit tiene número de consultas lineal en el tamaño de la fórmula. -/
theorem searchToDecisionQueries_polynomial :
    IsPolynomialBounded SAT.size searchToDecisionQueries 1 := by
  refine ⟨1, ?_⟩
  intro φ
  have h := Formula.varBound_le_size φ
  simp [searchToDecisionQueries]
  omega

/-- Obligación exacta que habría que probar para afirmar que el bucle es `O(log n)`. -/
def SearchToDecisionLogObligation : Prop :=
  IsPolyLogBounded SAT.size searchToDecisionQueries logn

/-! ## Interfaz rigurosa para PCP: verificador, no decidor por fuerza bruta -/

/--
Interfaz de un verificador PCP/holográfico para SAT.
No se identifica con un decidor de SAT: verifica una prueba/certificado.
-/
structure PCPVerifierForSAT where
  Proof : Type
  Randomness : Type
  verify : Formula → Proof → Randomness → Bool
  verifierSteps : Formula → Nat
  verifierBound : IsPolyLogBounded SAT.size verifierSteps logn
  completeness : ∀ φ : Formula, SAT.yes φ → ∃ π : Proof, ∀ r, verify φ π r = true
  soundness : ∀ φ : Formula, (¬ SAT.yes φ) → ∀ π : Proof, ∃ r, verify φ π r = false

/-- Obligación exacta del paper si se quiere convertir PCP en decidor de SAT en `O(log n)`. -/
def PCPDecisionObligation : Prop :=
  Nonempty (TimedDecider SAT logn)

/-! ## Complejidad formal del anidamiento -/

def pcpOrder : PolyLog := logn
theorem pcp_is_logn : pcpOrder = logn := rfl

def searchOrder : PolyLog := logn
theorem search_is_logn : searchOrder = logn := rfl

/-- Aritmética de órdenes: este sí es un teorema cerrado. -/
theorem total_complexity : PolyLog.nest searchOrder pcpOrder = log2n := by
  rw [search_is_logn, pcp_is_logn]
  rfl

/--
Teorema condicional mínimo: si existe realmente un decidor de SAT en `O(log² n)`,
entonces SAT está en P con cota formal sobre `steps`.
-/
def SAT_in_P_from_log2_decider (h : TimedDecider SAT log2n) : InPAlg SAT :=
  polylog_subset_P_alg SAT log2n h

/-! ## Verificaciones -/

abbrev x0 : Formula := Formula.var 0
abbrev not_x0 : Formula := Formula.neg x0
abbrev tautology : Formula := Formula.disj x0 not_x0
abbrev contradiction : Formula := Formula.conj x0 not_x0

#eval Formula.size tautology
#eval searchToDecisionQueries tautology
#eval (PolyLog.nest logn logn).exp
#eval decide (PolyLog.nest logn logn = log2n)

#check IsPolyLogBounded
#check TimedDecider
#check searchToDecisionQueries_polynomial
#check SearchToDecisionLogObligation
#check PCPVerifierForSAT
#check PCPDecisionObligation
#check total_complexity
#check SAT_in_P_from_log2_decider

#print axioms total_complexity
#print axioms searchToDecisionQueries_polynomial
#print axioms polylog_subset_P_alg

end PNPRigorousTime
