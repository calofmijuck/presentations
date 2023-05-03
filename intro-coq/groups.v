Require Import Ensembles.

Arguments In {U}.

Section Basic_laws.

Variable T : Type.
Variable op : T -> T -> T.

Notation "x * y" := (op x y).

Definition commutative :=
  forall x y : T, x * y = y * x.

Definition associative :=
  forall x y z : T, x * (y * z) = (x * y) * z.

Definition left_identity (e : T) :=
  forall x : T, e * x = x.

Definition right_identity (e : T) :=
  forall x : T, x * e = x.

Definition left_inverse (inv : T -> T) (e : T) :=
  forall x : T, (inv x) * x = e.

Definition right_inverse (inv : T -> T) (e : T) :=
  forall x : T, x * (inv x) = e.

Variable X : Ensemble T.

Definition endo_function (f : T -> T) :=
  forall x : T, In X x -> In X (f x).

Definition endo_operation (op : T -> T -> T) :=
  forall x y : T, In X x -> In X y -> In X (op x y).

End Basic_laws.

Hint Unfold commutative associative left_identity right_identity left_inverse right_inverse endo_function endo_operation.

Section group_definition.

Variable T : Type.

Record Group : Type := group
  {
    _G : Ensemble T;
    _op : T -> T -> T;
    _inv : T -> T;
    _e : T;
    _G0_closed : endo_operation T _G _op;
    _G1_assoc : associative T _op;
    _G2_id_exist : In _G _e;
    _G2_left_identity : left_identity T _op _e;
    _G2_right_identity : right_identity T _op _e;
    _G3_inv_exist : endo_function T _G _inv;
    _G3_left_inv : left_inverse T _op _inv _e;
    _G3_right_inv : right_inverse T _op _inv _e
  }.

End group_definition.

Section group_basic_properties.

Variable T : Type.
Variable Gr : Group T.

(* Group *)
Let G : Ensemble T := _G T Gr.

(* Binary Operation *)
Let op : T -> T -> T := _op T Gr.

Notation "x * y" := (op x y).

(* Inverse map *)
Let inv : T -> T := _inv T Gr.

(* Identity *)
Let e : T := _e T Gr.

(* binary operation is closed *)
Definition G0_closed :
  forall a b : T, In G a -> In G b -> In G (a * b) := _G0_closed T Gr.

(* binary operation is associative *)
Definition G1_assoc :
  forall a b c : T, a * (b * c) = (a * b) * c := _G1_assoc T Gr.

(* group has an identity element *)
Definition G2_id_exist : In G e := _G2_id_exist T Gr.

(* e * a = a for all a *)
Definition G2_left_identity :
  forall a : T, e * a = a := _G2_left_identity T Gr.

(* a * e = a for all a *)
Definition G2_right_identity :
  forall a : T, a * e = a := _G2_right_identity T Gr.

(* all elements in a group have an inverse *)
Definition G3_inv_exist :
  forall a : T, In G a -> In G (inv a) := _G3_inv_exist T Gr.

(* a * a^-1 = e *)
Definition G3_left_inv :
  forall a : T, (inv a) * a = e := _G3_left_inv T Gr.

(* a^-1 * a = e *)
Definition G3_right_inv :
  forall a : T, a * (inv a) = e := _G3_right_inv T Gr.

Hint Resolve G0_closed G1_assoc G2_id_exist G2_left_identity G2_right_identity G3_inv_exist G3_left_inv G3_right_inv.

Theorem cancel_left :
  forall a b : T, (inv a) * (a * b) = b.
Proof.
  intros a b.
  rewrite G1_assoc.
  rewrite G3_left_inv.
  rewrite G2_left_identity.
  reflexivity.
Qed.

(* skip *)
Theorem cancel_right :
  forall a b : T, (a * b) * (inv b) = a.
Proof.
  intros a b.
  rewrite <- G1_assoc.
  rewrite G3_right_inv.
  eauto. (* we can just use eauto. *)
Qed.

Theorem multiply_left :
  forall a b c : T, a = b -> c * a = c * b.
Proof.
  intros a b c H.
  rewrite H.
  reflexivity.
Qed.

(* skip *)
Theorem multiply_right :
  forall a b c : T, a = b -> a * c = b * c.
Proof.
  intros a b c H.
  rewrite H.
  reflexivity.
Qed.

Theorem solve_linear_left :
  forall a b x : T, a * x = b -> x = (inv a) * b.
Proof.
  intros.
  apply multiply_left with (c := inv a) in H.
  rewrite cancel_left in H.
  exact H.
Qed.

(* skip *)
Theorem solve_linear_right :
  forall a b x : T, x * a = b -> x = b * (inv a).
Proof.
  intros.
  apply multiply_right with (c := inv a) in H.
  rewrite cancel_right in H.
  exact H.
Qed.

Theorem resolve_left :
  forall a b : T, b * a = e -> b = inv a.
Proof.
  intros.
  apply solve_linear_right in H.
  rewrite G2_left_identity in H.
  exact H.
Qed.

(* skip *)
Theorem resolve_right : forall a b : T,
  a * b = e -> b = inv a.
Proof.
  intros.
  apply solve_linear_left in H.
  rewrite G2_right_identity in H.
  exact H.
Qed.

Theorem identity_inverse : e = inv e.
Proof.
  apply resolve_right.
  apply G2_left_identity.
Qed.

Theorem inv_involution :
  forall a : T, a = inv (inv a).
Proof.
  intros a.
  apply resolve_right.
  apply G3_left_inv.
Qed.

Theorem inverse_two:
  forall a b : T, (inv b) * (inv a) = inv (a * b).
Proof.
  intros.
  apply resolve_right.
  rewrite (G1_assoc (a * b) (inv b) (inv a)).
  rewrite cancel_right.
  apply G3_right_inv.
Qed.

Theorem left_cancellation :
  forall a b c: T, c * a = c * b -> a = b.
Proof.
  intros a b c H.
  apply solve_linear_left in H.
  rewrite cancel_left in H.
  exact H.
Qed.

(* skip *)
Theorem right_cancellation :
  forall a b c : T, a * c = b * c -> a = b.
Proof.
  intros a b c H.
  apply solve_linear_right in H.
  rewrite cancel_right in H.
  exact H.
Qed.

Theorem order_two_commutative:
  (forall (x : T), x * x = e) -> (forall a b : T, a * b = b * a).
Proof.
  intros order2 a b.
  assert (inv_self: forall x : T, x = inv x). {
    intros. apply resolve_right, order2.
  }

  assert (goal: a * b * (inv a) * (inv b) = e). {
    replace (inv a) with a.
    replace (inv b) with b.
    rewrite <- G1_assoc with (a := (a * b)).
    apply order2.
    apply inv_self.
    apply inv_self.
  }

  apply solve_linear_right in goal.
  apply solve_linear_right in goal.
  rewrite <- inv_involution in goal.
  rewrite <- inv_involution in goal.
  rewrite G2_left_identity in goal.
  exact goal.
Qed.

Fixpoint exp (x : T) (n : nat) :=
  match n with
  | O => e
  | S n' => x * exp x n'
  end.

Theorem commutative_exponent_law :
  (forall a b : T, a * b = b * a) ->
  (forall (a b : T) (n : nat), exp (a * b) n = exp a n * exp b n).
Proof.
  intros commutative a b.
  induction n.
  - simpl.
    rewrite G2_left_identity.
    reflexivity.
  - simpl.
    rewrite IHn.
    rewrite <- G1_assoc.
    rewrite (G1_assoc b (exp a n) (exp b n)).
    replace (b * exp a n) with (exp a n * b).
    + repeat rewrite G1_assoc.
      reflexivity.
    + apply commutative.
Qed.

End group_basic_properties.
