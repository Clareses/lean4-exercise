-- Prove the following identities, replacing the "sorry" placeholders with actual proofs.

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h: p ∧ q => And.intro (And.right h) (And.left h))
    (fun h: q ∧ p => And.intro (And.right h) (And.left h))

def f := fun h: p ∨ q =>
  show q ∨ p from
  Or.elim
    h
    (fun hp: p => show q ∨ p from Or.intro_right q hp)
    (fun hq: q => show q ∨ p from Or.intro_left p hq)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h: p ∨ q => show q ∨ p from f p q h)
    (fun h: q ∨ p => show p ∨ q from f q p h)


-- associativity of ∧ and ∨

def f1 := fun h: (p ∧ q) ∧ r =>
  show p ∧ (q ∧ r) from
  (And.intro
    (And.left (And.left h))
    (And.intro
      (And.right (And.left h))
      (And.right h)
    )
  )

def f2 := fun h: p ∧ (q ∧ r) =>
  show (p ∧ q) ∧ r from
  ⟨⟨And.left h, And.left (And.right h)⟩, And.right (And.right h)⟩

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h: (p ∧ q) ∧ r => show p ∧ (q ∧ r) from (f1 p q r h))
    (fun h: p ∧ (q ∧ r) => show (p ∧ q) ∧ r from (f2 p q r h))



example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
  (fun h: (p ∨ q) ∨ r => show p ∨ (q ∨ r) from Or.elim h
    (fun h': p ∨ q => show p ∨ (q ∨ r) from Or.elim h'
      (fun h'': p => show p ∨ (q ∨ r) from @Or.inl p (q ∨ r) h'')
      (fun h'': q => show p ∨ (q ∨ r) from @Or.inr p (q ∨ r) (Or.inl h'')))
    (fun h': r => Or.inr (Or.inr h')))
  (fun h: p ∨ (q ∨ r) => show (p ∨ q) ∨ r from Or.elim h
    (fun h': p => show (p ∨ q) ∨ r from @Or.inl (p ∨ q) r (@Or.inl p q h'))
    (fun h': q ∨ r => show (p ∨ q) ∨ r from Or.elim h'
      (fun h'': q => Or.inl (Or.inr h''))
      (fun h'': r => Or.inr h'')))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
  (fun h: p ∧ (q ∨ r) => show (p ∧ q) ∨ (p ∧ r) from
    (Or.elim (h.right)
      (fun h': q => (@Or.inl (p ∧ q) _ ⟨h.left, h'⟩))
      (fun h': r => (@Or.inr _ (p ∧ r) ⟨h.left, h'⟩))))
  (fun h: (p ∧ q) ∨ (p ∧ r) => show p ∧ (q ∨ r) from
    (@And.intro p (q ∨ r)
      (Or.elim h (fun h': p ∧ q => h'.left) (fun h': p ∧ r => h'.left))
      (Or.elim h
        (fun h': p ∧ q => Or.inl h'.right)
        (fun h': p ∧ r => Or.inr h'.right))))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  (Iff.intro
    (λ h: p ∨ (q ∧ r) => show (p ∨ q) ∧ (p ∨ r) from
      (@And.intro (p ∨ q) (p ∨ r)
        (Or.elim h
          (λ h': p => @Or.inl p q h')
          (λ h': q ∧ r => Or.inr h'.left))
        (Or.elim h
          (λ h': p => Or.inl h')
          (λ h': q ∧ r => Or.inr h'.right))))
    (λ h: (p ∨ q) ∧ (p ∨ r) => show p ∨ (q ∧ r) from
      (Or.elim h.left
        (λ h': p => show p ∨ (q ∧ r) from Or.inl h')
        (λ h': q => show p ∨ (q ∧ r) from
          (Or.elim h.right
            (λ h'': p => Or.inl h'')
            (λ h'': r => Or.inr (And.intro h' h'')))))))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := (Iff.intro
  (fun h: p → (q → r) => show p ∧ q → r from
    (fun h': p ∧ q => h h'.left h'.right))
  (fun h: p ∧ q → r => show p → (q → r) from
    (fun h': p => (fun h'': q => show r from h ⟨h', h''⟩))))

-- 欲证明一个定理，就构造一个函数即可
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := (Iff.intro
  (fun h: (p ∨ q) → r => show (p → r) ∧ (q → r) from
    (And.intro
      (fun f: p => show r from h (Or.inl f))
      (fun f: q => show r from h (Or.inr f))))
  (fun h: (p → r) ∧ (q → r) => show (p ∨ q) → r from
    (fun h': p ∨ q => show r from
      (Or.elim h'
      (fun f: p => h.left f)
      (fun f: q => h.right f)))))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := (Iff.intro
  (fun h: ¬ (p ∨ q) => show ¬ p ∧ ¬ q from
    (And.intro
      (show ¬ p from (fun f: p => h (Or.inl f)))
      (show ¬ q from (fun f: q => h (Or.inr f)))))
  (fun h: ¬ p ∧ ¬ q => show ¬ (p ∨ q) from
    (Not.intro (show p ∨ q → False from
      (fun h': p ∨ q => show False from
        (Or.elim h'
          (fun f: p => h.left f)
          (fun f: q => h.right f)))))))

example : ¬p ∨ ¬q → ¬ (p ∧ q) :=
  (fun h: ¬ p ∨ ¬ q => show ¬ (p ∧ q) from
    (Not.intro (show p ∧ q → False from
      (fun h': p ∧ q => show False from
        (Or.elim h
          (fun f: ¬ p => f h'.left)
          (fun f: ¬ q => f h'.right))))))

example : ¬(p ∧ ¬p) := fun h: p ∧ ¬ p => show False from h.right h.left

example : p ∧ ¬q → ¬(p → q) :=
  (fun h: p ∧ ¬ q => show ¬ (p → q) from
    (fun h': p → q => show False from h.right (h' h.left)))

example : ¬p → (p → q) :=
  (fun h: ¬ p => show p → q from
    (fun h': p => show q from False.elim (h h')))

example : (¬p ∨ q) → (p → q) :=
  fun h: ¬ p ∨ q => show p → q from
  fun h': p => show q from
  Or.elim h
  (fun f: ¬ p => @False.elim q (f h'))
  (fun f: q => f)

example : p ∨ False ↔ p := (Iff.intro
  (fun h: p ∨ False => show p from
    (Or.elim h
    (fun f: p => f)
    (fun f: False => @False.elim p f)))
  (fun h: p => show p ∨ False from
    (@Or.intro_left p False h)))

example : p ∧ False ↔ False := (Iff.intro
  (fun h: p ∧ False => show False from h.right)
  (fun h: False => show p ∧ False from
    (And.intro (@False.elim p h) h)))

example : (p → q) → (¬q → ¬p) :=
  (fun h: p → q => show ¬ q → ¬ p from
    (fun h': ¬ q => show ¬ p from
      (fun h'': p => show False from
        (h' (h h'')))))

-- Prove the following identities, replacing the "sorry" placeholders with actual proofs. These require classical reasoning.
open Classical

open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun h: p → q ∨ r => show (p → q) ∨ (p → r) from
  @byCases p ((p → q) ∨ (p → r))
  (show p → ((p → q) ∨ (p → r)) from
    (fun h': p => (Or.elim (h h')
      (fun f: q => Or.inl (fun _: p => f))
      (fun f: r => Or.inr (fun _: p => f)))))
  (show ¬ p → (p → q) ∨ (p → r) from
    (fun h': ¬ p => Or.inl (show p → q from
      (fun f: p => False.elim (h' f)))))

example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry
