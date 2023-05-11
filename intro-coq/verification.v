Module AExp.

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

(* 1 + 3 * 2 is turned into *)
Definition seven :=
  APlus (ANum 1) (AMult (ANum 3) (ANum 2)).

(* 3 * 7 - 10 is turned into *)
Definition eleven :=
  AMinus (AMult (ANum 3) (ANum 7)) (ANum 10).

(* Evaluate aexp *)
Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus  a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult  a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval:
  aeval seven = 7 /\ aeval eleven = 11.
Proof. split; reflexivity. Qed.

(* Optimize the expression *)
Fixpoint aeval_optimize (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus a1 a2 => APlus (aeval_optimize a1) (aeval_optimize a2)
  | AMinus a1 a2 => AMinus (aeval_optimize a1) (aeval_optimize a2)
  | AMult (ANum 0) _ => ANum 0
  | AMult a1 a2 => AMult (aeval_optimize a1) (aeval_optimize a2)
  end.

(* Prove correctness of optimization *)
Theorem optimize_correct: forall (a : aexp),
  aeval (aeval_optimize a) = aeval a.
Proof.
  induction a.
  - simpl. auto.
  - simpl. rewrite IHa1, IHa2. auto.
  - simpl. rewrite IHa1, IHa2. auto.
  - destruct a1.
    + destruct n. simpl. auto. simpl in *.
      rewrite IHa2. auto.
    + simpl in *. rewrite IHa1, IHa2. auto.
    + simpl in *. rewrite IHa1, IHa2. auto.
    + simpl in *. rewrite IHa1, IHa2. auto.
Qed.

(* Coq: The Proof Assistant *)
Theorem optimize_correct_auto: forall (a : aexp),
  aeval (aeval_optimize a) = aeval a.
Proof.
  (* EZ *)
  induction a; simpl; auto.
  destruct a1; simpl; auto;
  destruct n; simpl; auto.
Qed.

(* Optimize the expression *)
Fixpoint optimize_mult (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus a1 a2 => APlus (optimize_mult a1) (optimize_mult a2)
  | AMinus a1 a2 => AMinus (optimize_mult a1) (optimize_mult a2)
  | AMult (ANum 0) _ => ANum 0
  (* Added case *)
  | AMult _ (ANum 0) => ANum 0
  | AMult a1 a2 => AMult (optimize_mult a1) (optimize_mult a2)
  end.

(*
  We cannot apply the same proof,
  since there are more cases to consider.
*)
Theorem optimize_mult_correct: forall (a : aexp),
  aeval (optimize_mult a) = aeval a.
Proof.
  (* Remove 3 goals *)
  induction a; simpl; auto.

  (* Creates 16 goals... *)
  (* destruct a1, a2. *)

  (* Handles all of them *)
  destruct a1, a2; simpl; auto;
  destruct n; simpl; auto;
  destruct n0; simpl; auto.
Qed.

(*
  If we were to try optimizing further,
  we would get many more cases to consider.

  Since the proof for each case is similar,
  they can be handled in the same way using automation.
*)
