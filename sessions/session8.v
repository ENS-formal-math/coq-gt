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

(* coercion *)

Section CoercionExample.

Fail Example bool_theorem : Nat.eqb 2 2.

(* f: C -> D is a coercion iff
   - D is user defined class : f: ... -> D
   - D is Funclass (A -> B): f: ... -> A -> B
   - D is Sortclass (Type, Set, Prop): f: ... -> sort *)

Definition is_true b := b = true.
Check is_true.

Coercion is_true : bool >-> Sortclass. (* Prop *)

Example bool_theorem : Nat.eqb 2 2.
Proof. reflexivity. Qed.

End CoercionExample.

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

(* In order for Coq to know which type to wrap inside eqType, we have
   to present a canonical solution *)

Definition nat_eqMixin := Equality.Mixin nat Nat.eqb nat_refl.
Canonical nat_eqType := @Equality.Pack nat nat_eqMixin.

(* Now Coq internally has a global table of solutions
   nat -> nat_eqType which it's able to use. 
   It is useful since we can define a Record type with some functionality and
   then define new canonical solution for some external type T, which will immediately
   enjoy all prooved properties *)

Compute (3 == 3).

Example nat_eq: (2 + 1 == 3).
Proof. simpl. reflexivity. Qed.

(* In order to see how this section works, 
   unfortunately you have to comment out Canonical nat_eqType definition, since 
   it's already defined globablly in Coq *)

Module WrongEqType.

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

Example test: (2 + 1 == 3) = true.
Proof.
    unfold eq_op. unfold nat_eqTypeWrong. simpl. destruct nat_eqMixin.
    simpl. specialize (r 3 3). inversion r.
    - reflexivity.
    - destruct np. reflexivity.
Qed.

Module WrongEqType.

(* We uncovered that the probelm with Module WrongEqType is that 
   when we define nat_eqMixin using Proof and Qed, Coq totally forgets the proof object itself.
   Therefore, it cannot compute the result of 2 + 1 == 3. What we proved in theorem test
   is an actual proof of 2 + 1 == 3 from bare axiom included in nat_eqMixin that
   operation op reflects equality = 
   Thus, the correct way to define nat_eqMixin using proof mode is given below.
   (to see it we have to again comment out the previous canonical definitions )*)

Module WrongEqTypeFixed.

Definition nat_eqMixin : Equality.mixin_of nat.
    apply (Equality.Mixin nat Nat.eqb). apply nat_refl.
Defined.

Canonical nat_eqType := @Equality.Pack nat nat_eqMixin.

Example test: (2 + 1 == 3).
Proof. reflexivity. Qed.

Module WrongEqTypeFixed.

