(* Start with simple types *)
Inductive bool : Type :=
  | true
  | false.

(* invert booleans *)
Definition neg (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

(* simple proof *)
Example not_false_eq_true: neg false = true.
Proof.
  simpl.
  reflexivity.
Qed.

Definition and (b1 b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition or (b1 b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Notation "x && y" := (and x y).
Notation "x || y" := (or x y).

Example bool_operation:
  (true && false) || false = false.
Proof.
  auto.
Qed.

(* Case Analysis *)
Theorem de_morgan_and: forall (a b : bool),
  neg (a && b) = (neg a) || (neg b).
Proof.
  destruct a, b.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem de_morgan_or: forall (a b : bool),
  neg (a || b) = (neg a) && (neg b).
Proof.
  destruct a, b; auto.
Qed.

Module NatPlayground.

(* Move on to natural numbers *)
Inductive nat : Type :=
  | O
  | S (n : nat).

Fixpoint plus (n m: nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

End NatPlayground.

(* proof = program *)
Definition add_O_n_def:
  forall n : nat, 0 + n = n :=
  fun n => eq_refl n.

(* proving a theorem = building a program *)
Theorem add_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n.
  reflexivity.
  Show Proof.
Qed.

(* Induction *)
(* Program that checks P(0) *)
(* Program that checks P(n + 1) from P(n) *)
Check nat_ind : forall P : nat -> Prop,
  P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n.

Theorem add_identity_right:
  forall n : nat, n + 0 = n.
Proof.
  intros n.
  simpl. (* doesn't work *)

  induction n.
  - auto.
  - simpl. rewrite IHn. reflexivity.
Qed.

(* automation *)
Theorem add_identity_right':
  forall n : nat, n + 0 = n.
Proof.
  induction n; auto.
Qed.

Lemma add_reorder:
  forall n m : nat, n + S m = S (n + m).
Proof.
  (* creates 4 goals... :( *)
  (* induction n, m. *)

  (* automation *)
  induction n, m; try rewrite IHn; auto.
Qed.

(* solving arithmetic goals over ordered rings *)
Require Import Psatz.

Fixpoint square_sum (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n * n + square_sum n'
  end.

(* a familiar equation *)
Theorem square_sum_correct: forall n : nat,
  6 * square_sum n = n * (n + 1) * (2 * n + 1).
Proof.
  induction n.
  - trivial.
  (* magic *)
  - simpl square_sum. nia.
Qed.

(* Logic *)
(* Propositions *)
Theorem add_right_eq: forall a b c: nat,
  a = b -> a + c = b + c.
Proof.
  intros a b c H.
  auto.
Qed.

(* And *)
Theorem zero_sum: forall n m : nat,
  n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn, Hm.
  reflexivity.
Qed.

(* Or *)
Theorem zero_mult: forall n m : nat,
  n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m H.

  (* Creates two goals *)
  destruct H.
  - rewrite H. auto.
  - rewrite H. auto.

  (* destruct H; rewrite H; auto. *)
Qed.

(* Exists *)
Theorem forall_not_ex_not: forall (P: nat -> Prop),
  (forall n : nat, P n) -> ~ exists n, ~ P n.
Proof.
  unfold not.
  intros P ALL.
  intros NONE.
  destruct NONE.
  apply H.
  apply ALL.
Qed.

Theorem disjunction_implies_all:
  forall (P Q R : nat -> Prop),
  (exists x, P x \/ Q x) /\
  (forall x, P x -> R x) /\
  (forall x, Q x -> R x)
  -> exists x, R x.
Proof.
  intros P Q R H.
  destruct H as [PorQ [PR QR]].
  destruct PorQ.
  destruct H as [HP | HQ]; eauto.
Qed.
