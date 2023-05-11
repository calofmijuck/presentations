Definition excluded_middle :=
  forall P : Prop, P \/ ~ P.

Theorem excluded_middle_equiv_double_neg:
  excluded_middle <-> (forall P : Prop, ~~P -> P).
Proof.
  unfold excluded_middle, not. split.
  - intros excluded_middle P.
    assert (p_excluded: P \/ ~P). eauto.
    destruct p_excluded as [HP | HNP]; eauto.
    tauto.
  - intros double_neg_implies_p P.
    apply double_neg_implies_p.
    auto.
Qed.
