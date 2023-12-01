(* Reflection Session *)

Inductive reflect (P: Prop): bool -> Prop :=
| ReflectT (p: P): reflect P true
| ReflectF (np: ~P): reflect P false.

(* typical example *)

Section ListHas.

Require Import List.
Import ListNotations.

(* boolean definition *)

Fixpoint has {T} (a: T -> bool) (l: list T) : bool := 
    match l with
    | [] => false
    | x :: l' => orb (a x) (has a l')
    end.

(* indexed definition *)

Fixpoint length {T} (l : list T): nat :=
    match l with 
    | [] => O
    | x :: l' => S (length l')
    end.

Fixpoint nth {T} (n : nat) (l : list T) (default : T) : T :=
    match n with
    | 0 => match l with
           | [] => default
           | x :: _ => x
           end
    | S m => match l with
             | [] => default
             | _ :: t => nth m t default
             end
    end.

Definition has_indexed {T} (a: T -> bool) (l: list T) : Prop :=
    exists default: T, exists i, i < length l /\ a (nth i l default) = true.

(* proposotional reflection *)

Inductive has_prop {T} (a: T -> bool) : list T -> Prop :=
    | head (x : T) (l: list T) (H: a x = true): has_prop a (x :: l)
    | next (x : T) (l: list T) (H: has_prop a l): has_prop a (x :: l).

(* finite list example *)

Example has_fin: has (fun x => Nat.eqb x 1) [3;1;2] = true.
Proof. reflexivity. Qed.

Example has_indexed_fin: has_indexed (fun x => Nat.eqb x 1) [3;1;2].
Proof.
    exists 0, 1. simpl. split.
    - apply le_S. apply le_n.
    - reflexivity.
Qed.

Example has_prop_fin: has_prop (fun x => Nat.eqb x 1) [3;1;2].
Proof.
    apply next. apply head. reflexivity.
Qed.

Create HintDb has_db.
Hint Constructors has_prop : has_db.

Example has_prop_auto_fin: has_prop (fun x => Nat.eqb x 1) [3;1;2].
Proof.
    auto with has_db.
Qed.

End ListHas.

(* equality reflection *)

Module Equality.

Definition rel (T: Type) := T -> T -> bool.

Record mixin_of T := Mixin {
    op: rel T; 
    _ : forall x y, reflect (x = y) (op x y)
}.

Record type: Type := Pack {
    sort :> Type;
    class : mixin_of sort
}.

End Equality.

Notation eqType := Equality.type.

Check Equality.op.
Check Equality.class.

Definition eq_op T := Equality.op _ (Equality.class T).
Notation "x == y" := (@eq_op _ x y) (at level 70).

(* Example of reflection definition for integers *)

Theorem nat_refl: forall x y, reflect (x = y) (Nat.eqb x y).
Proof.
    intro x; induction x; intro y.
    - destruct y. 
        + apply ReflectT. reflexivity.
        + apply ReflectF. discriminate.
    - destruct y.
        + apply ReflectF. discriminate.
        + simpl. specialize (IHx y). destruct (Nat.eqb x y).
            * apply ReflectT. inversion IHx. rewrite p. reflexivity.
            * apply ReflectF. inversion IHx. intro G. 
              injection G. apply np.
Qed.        

Section WrongEqType.

Definition nat_eqMixin : Equality.mixin_of nat.
Proof.
    apply (Equality.Mixin nat Nat.eqb). apply nat_refl.
Qed.

Print nat_eqMixin.

Canonical nat_eqType := @Equality.Pack nat nat_eqMixin.

Compute (2 + 1 == 3).
(*
    We get 
    = match nat_eqMixin with
        | {| Equality.op := op |} => op
        end 3 3
        : bool
*)
Unset Printing Notations.

Example test: (2 + 1 == 3) = true.
Proof.
    unfold eq_op. unfold nat_eqType.
    simpl. destruct nat_eqMixin. specialize (r 3 3). inversion r.
    - symmetry. unfold eq_op. unfold nat_eqType. simpl. apply H0.

End WrongEqType.

Definition nat_eqMixin := Equality.Mixin nat Nat.eqb nat_refl.

Example nat_eq: (2 + 1 == 3) = true.
Proof. simpl. reflexivity. Qed.
