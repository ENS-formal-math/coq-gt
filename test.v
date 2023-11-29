Inductive test : Type := 
  | foo
  | bar.

Definition f t := match t with 
  | foo => true
  | bar => false
  end.

Theorem true_foo : forall t, f t = true -> t = foo.
Proof.
destruct t; intros H; try reflexivity; discriminate.
Qed.