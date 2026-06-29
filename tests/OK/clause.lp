require open tests.OK.boolean;
symbol Prop : TYPE;
//symbol Clause : TYPE ≔ Prop;
//symbol ⟇ : Clause → Clause → Clause;
//notation ⟇ infix right 22;
//symbol ▩ : Clause;
//symbol 𝔹: TYPE ≔ B;
symbol and : B → B → B; notation and infix 50;
rule $x and true ↪ $x;
rule true and $x ↪ $x;
//rule _ and false ↪ false;
//rule false and _ ↪ false;

symbol ℂ: TYPE;
symbol P: Prop → ℂ;
right associative commutative symbol ⊔: ℂ → ℂ → ℂ; notation ⊔ infix right 2;
//left associative commutative symbol ⊔: ℂ → ℂ → ℂ; notation ⊔ infix left 2;
symbol ⬓: ℂ;

//symbol F: Clause → ℂ;

//rule F ($x ⟇ $xs) ↪ (P $x) ⊔ (F $xs)
//with F ▩ ↪ ⬓
//;

sequential symbol  ⩦: ℂ → ℂ → B; notation ⩦ infix 11;
rule (P $x) ⩦ (P $x) ↪ true
with (P $x) ⩦ (P $y) ↪ false
with ($x ⊔ $xs) ⩦ ($y ⊔ $ys) ↪ ($x ⩦ $y) and ($xs ⩦ $ys)
with ⬓ ⩦ ⬓ ↪ true
with ⬓ ⩦ (P _) ↪ false
with (P _) ⩦ ⬓ ↪ false
with (_ ⊔ _) ⩦ ⬓ ↪ false
with ⬓ ⩦ (_ ⊔ _) ↪ false
with (P _) ⩦ (_ ⊔ _) ↪ false
with (_ ⊔ _) ⩦ (P _) ↪ false;

// Checking that associativity steps count
symbol c: ℂ;
compute (c ⊔ (c ⊔ c));
compute ((c ⊔ c) ⊔ c);
assert ⊢ (c ⊔ (c ⊔ c)) ≡ ((c ⊔ c) ⊔ c);

// Checking that associativity steps count
symbol a : Prop;
symbol b : Prop;
compute (P b ⊔ P a ⊔ ⬓);
compute (P a ⊔ P b ⊔ ⬓);

assert ⊢ (P a ⊔ ⬓)  ≡  (⬓ ⊔ P a);
compute (P a ⊔ ⬓)  ⩦  (⬓ ⊔ P a);
assert ⊢ (P a ⊔ ⬓)  ⩦  (⬓ ⊔ P a) ≡ true;

compute ((P b ⊔ P a ⊔ ⬓)  ⩦  (P a ⊔ P b ⊔ ⬓)); // No AC computed here
assert ⊢ (P b ⊔ P a ⊔ ⬓)  ⩦  (P a ⊔ P b ⊔ ⬓) ≡ true;
