import Init.Data.Vector


inductive Form (α : Type)
  | bot : Form α
  | atoms : α  → Form α
  | neg : Form α → Form α
  | and : Form α → Form α → Form α
  | or : Form α → Form α → Form α
  | imp : Form α → Form α → Form α

@[simp]
def sizeOf_Form : Form α → Nat
  | .bot => 0
  | .atoms _ => 1
  | .neg f => 1 + sizeOf_Form f
  | .and p q => 1 + sizeOf_Form p + sizeOf_Form q
  | .or p q => 1 + sizeOf_Form p + sizeOf_Form q
  | .imp p q => 1 + sizeOf_Form p + sizeOf_Form q

-- not  in prop, so you can put it in a list
inductive In (a : α) : List α → Type
  /-- The head of a list is a member: `a ∈ a :: as`. -/
  | head {as : List α} : a = y → In a (y::as)
  /-- A member of the tail of a list is a member of the list: `a ∈ l → a ∈ b :: l`. -/
  | tail {b : α} {as : List α} : In a as → In a (b::as)

-- Γ ⊢ x
--It is of Type u+1 bc of α being in Type 1. Is this problem?
inductive Sequent α
  | seq : (context : List (Form α )) → Form α → Sequent α

-- [x, y], [f1, f2], [true, false] ⊢ f
inductive Seq4Proof α
  | seq4 : List α  → (g: List (Form α)) → Vector Bool g.length → Form α → Seq4Proof α

inductive Proof : Sequent α → Type
  | ax :
    ∀ {a : Form α } {Γ : List (Form α )},
    In a Γ  → Proof (.seq Γ a)
  | botl :
    ∀ {a : Form α} {Γ : List (Form α)},
    In .bot Γ → Proof (.seq Γ a)
  | negr :
    ∀ {a : Form α } {Γ : List (Form α )},
    In a Γ → Proof (.seq Γ .bot) → Proof (.seq Γ (.neg a))
  | negl :
    ∀ {a b: Form α } {Γ : List (Form α )},
    In (.neg a) Γ → Proof (.seq Γ a) → Proof (.seq Γ b)
  | andl :
    ∀ {a b c: Form α } {Γ : List (Form α)},
    In a Γ → In b Γ →
    In (.and a b) Γ →
    Proof (.seq Γ c)
  | andr :
    ∀ {a b: Form α } {Γ : List (Form α )},
    Proof (.seq Γ a) → Proof (.seq Γ b) → Proof (.seq Γ (.and a b))
  --sussus
  | orl :
    ∀ {a b c: Form α } {Γ : List (Form α )},
    Proof (.seq Γ a)→ Proof (.seq Γ b) → (In (.or a b) Γ → Proof (.seq Γ c))
--find proofs of x being in xs
def findAll [DecidableEq α ] (x : α) (xs : List α) : List (In x xs) :=
  match xs with
  | [] => []
  | y :: ys =>
    let recur := List.map In.tail (findAll x ys)
    match decEq x y with
    | .isTrue p => In.head p :: recur
    | .isFalse _ => recur
  -- if x = y then In.head ys :: findAll

--seperate atoms from forms
def getAtoms (g : List (Form α)) : List α :=
  match g with
  | [] => []
  | .atoms a :: ys => a :: getAtoms ys
  | _ :: ys => getAtoms ys

-- get the first form in our context, that we have not expanded
def getNonVisited (g : List (Form α)) (visited : Vector Bool g.length) : Option (Form α) :=
  match g with
  | [] => none
  | y :: ys =>
    match visited[0]? with
    | none => none
    | some b =>
      if b then
        getNonVisited ys (visited.tail)
      else
        some y

@[simp]
def seqAtoms2seq (s : Seq4Proof α) : Sequent α:=
  match s with
  | .seq4 atoms forms _ a =>
    Sequent.seq ((atoms.map .atoms) ++ forms) a

-- visited: true if we have looked at the formula
def automatedProof [DecidableEq α][DecidableEq (Form α)]
                   (s : Seq4Proof α):
                   List (Proof (seqAtoms2seq s)) :=
   -- 1. make sure everything is visited using the cases which check the formula on the left.
   -- 2. use the cases which consider the formula on the right.
  match s with
  | Seq4Proof.seq4 atoms forms visited a =>
    match getNonVisited forms visited with
    | none =>
        match a with
        | .atoms x =>
          have h := List.map Proof.ax (findAll (Form.atoms x) ((List.map Form.atoms atoms) ++ forms))
          by
          unfold seqAtoms2seq
          simp
          exact h
        | .bot => []

        | .neg x =>
          sorry
        | _ => sorry
    | .some p =>
      sorry


def automatedProofHelper [DecidableEq α][DecidableEq (Form α)] (s : Sequent α) : List (Proof s) :=
  match s with
  | .seq xs a =>
    let vector := Array.toVector (List.toArray (List.map (λ x => false) xs))
    by
      simp only [Array.size_toArray, List.length_map] at vector

      have ugh := automatedProof (Seq4Proof.seq4 [] xs vector a)
      unfold seqAtoms2seq at ugh
      simp at ugh
      exact ugh
