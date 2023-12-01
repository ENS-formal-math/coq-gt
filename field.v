Definition assoc (X : Type) (f : X -> X -> X) := forall x y z : X, f x (f y z) = f (f x y) z.

Definition comm (X : Type) (f : X -> X -> X) := forall x y : X, f x y = f y x.

Arguments assoc {X}. Arguments comm {X}.

Record Field : Type := makeField {
  K : Set;
  plus : K -> K -> K;
  times : K -> K -> K;

  zero : K;
  one : K;

  one_not_zero : zero <> one;
  plus_assoc : assoc plus;
  plus_comm : comm plus;
  times_assoc : assoc times;
  times_comm : comm times;
  distrib : forall x y z : K, times x (plus y z) = plus (times x y) (times x z);

  plus_0 : forall x : K, plus x zero = x;
  times_1 : forall x : K, times x one = x;

  plus_inv : forall x : K, exists y : K, plus x y = zero;
  mult_inv : forall x : K, x <> zero -> exists y : K, times x y = one;
  
  }.


Arguments K {f}.
Arguments plus {f}.
Arguments zero {f}.


Lemma zero_plus_zero : forall (F : Field), plus (@zero F) (zero ) = zero .
Proof. intros F. apply plus_0. Qed.


Fixpoint add_n_ones (f : Field) n := match n with 
  | 0 => @zero f
  | S m => plus (add_n_ones f m) (one f)
  end.


Definition charac_zero (f : Field) := forall (n : nat), add_n_ones f n = @zero f -> n = 0.



