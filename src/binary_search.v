From demo Require Import simplified_iris.
From stdpp Require Import list.

Open Scope Z_scope.

Definition insert: val :=
  rec: "insert" "t" "x" :=
    match: !"t" with
      NONE => "t" <- InjR ("x", (ref NONE, ref NONE))
    | SOME "node" =>
      let: "v" := Fst "node" in
      let: "l" := Fst (Snd "node") in
      let: "r" := Snd (Snd "node") in
      if: "x" = "v"
      then #()
      else (if: "x" < "v"
            then "insert" "l" "x"
            else "insert" "r" "x")
    end.

Definition search: val :=
  rec: "search" "t" "x" :=
    match: !"t" with
      NONE => #false
    | SOME "node" =>
      let: "v" := Fst "node" in
      let: "l" := Fst (Snd "node") in
      let: "r" := Snd (Snd "node") in
      if: "x" = "v"
      then #true
      else (if: "x" < "v"
            then "search" "l" "x"
            else "search" "r" "x")
    end.

Section proof.
Context `{!heapGS Σ}.
Implicit Types (t l r:loc).

Definition tree_pre (tree: loc -d> gset Z -d> iPropO Σ): loc -d> gset Z -d> iPropO Σ :=
  (λ t els, (⌜els = ∅⌝ ∧ t ↦ NONEV) ∨
    (∃ left_els right_els (key: Z) l r,
        ⌜els = {[key]} ∪ left_els ∪ right_els⌝ ∗
        ⌜∀ e, e ∈ left_els → e < key⌝ ∗
        ⌜∀ e, e ∈ right_els → key < e⌝ ∗
        t ↦ SOMEV (#key, (#l, #r)) ∗
        ▷ tree l left_els ∗ ▷ tree r right_els))%I.

Local Instance tree_pre_contractive : Contractive tree_pre.
Proof.
  rewrite /tree_pre=> n tree tree' Htree t els.
  repeat (f_contractive || f_equiv); apply Htree.
Qed.

Definition tree : loc → gset Z → iProp Σ := fixpoint tree_pre.

Theorem tree_unfold t els :
  tree t els ⊣⊢
  (⌜els = ∅⌝ ∧ t ↦ NONEV) ∨
    (∃ left_els right_els (key: Z) l r,
        ⌜els = {[key]} ∪ left_els ∪ right_els⌝ ∗
        ⌜∀ e, e ∈ left_els → e < key⌝ ∗
        ⌜∀ e, e ∈ right_els → key < e⌝ ∗
        t ↦ SOMEV (#key, (#l, #r)) ∗
        ▷ tree l left_els ∗ ▷ tree r right_els).
Proof. apply (fixpoint_unfold tree_pre). Qed.

Lemma tree_empty t :
  t ↦ NONEV -∗ tree t ∅.
Proof.
  iIntros "Ht".
  iApply tree_unfold; iLeft; auto.
Qed.

Theorem wp_tree_insert t (x:Z) els :
  {{{ tree t els }}}
    insert #t #x
  {{{ RET #(); tree t ({[x]} ∪ els) }}}.
Proof.
  iLöb as "IH" forall (t els).
  iIntros (Φ) "Ht HΦ".
  wp_rec; wp_pures.
  iDestruct (tree_unfold with "Ht") as "[Ht|Ht]".
  - iDestruct "Ht" as (->) "Ht".
    wp_load; wp_pures.
    wp_alloc r.
    wp_alloc l.
    wp_store.
    iApply "HΦ".
    iModIntro.
    iApply tree_unfold.
    iRight.
    iExists ∅, ∅, _, _, _.
    iFrame.
    iSplit; first by iPureIntro; set_solver.
    iSplit; first by iPureIntro; set_solver.
    iSplit; first by iPureIntro; set_solver.
    rewrite -!tree_empty.
    iFrame.
  - iDestruct "Ht" as (????? -> Hleft Hright) "(Ht&Hl&Hr)".
    wp_load; wp_pures.
    rewrite bool_decide_decide.
    destruct (decide (#x = #key)) as [Heqb|Heqb]; wp_pures.
    + iModIntro.
      inversion Heqb; subst.
      iApply "HΦ".
      rewrite !assoc_L.
      replace {[key; key]} with ({[key]}: gset Z) by set_solver.
      iApply tree_unfold; iRight.
      iExists left_els, right_els, _, _, _; iFrame.
      iPureIntro.
      split_and!; set_solver.
    + assert (x ≠ key) by (intros ->; auto).
      rewrite bool_decide_decide.
      destruct (decide (x < key)%Z) as [Heqb2|Heqb2]; wp_pures.
      * iApply ("IH" with "Hl").
        iIntros "!> Hl".
        iApply "HΦ".
        iApply tree_unfold; iRight.
        iExists ({[x]} ∪ left_els), right_els, _, _, _; iFrame.
        iPureIntro.
        set_solver.
      * iApply ("IH" with "Hr").
        iIntros "!> Hr".
        iApply "HΦ".
        iApply tree_unfold; iRight.
        iExists left_els, ({[x]} ∪ right_els), _, _, _; iFrame.
        iPureIntro.
        assert (key < x) by lia.
        set_solver.
Qed.

Theorem wp_tree_search t (x:Z) els :
  {{{ tree t els }}}
    search #t #x
  {{{ RET #(bool_decide (x ∈ els)); tree t els }}}.
Proof.
  iLöb as "IH" forall (t els).
  iIntros (Φ) "Ht HΦ".
  set (x_in_els:=bool_decide (x ∈ els)).
  wp_rec; wp_pures.
  iDestruct (tree_unfold with "Ht") as "[Ht|Ht]".
  - iDestruct "Ht" as (->) "Ht".
    wp_load; wp_pures.
    iApply "HΦ".
    by iApply tree_empty.
  - iDestruct "Ht" as (????? -> Hleft Hright) "(Ht&Hl&Hr)".
    wp_load; wp_pures.
    rewrite bool_decide_decide.
    destruct (decide (#x = #key)) as [Heqb|Heqb]; wp_pures.
    + inversion Heqb; subst.
      replace x_in_els with true.
      { iApply "HΦ".
        iApply tree_unfold; iRight.
        eauto 10 with iFrame. }
      rewrite /x_in_els.
      apply symmetry, bool_decide_eq_true.
      set_solver.
    + assert (x ≠ key) by (intros ->; auto).
      rewrite bool_decide_decide.
      destruct (decide (x < key)%Z) as [Heqb2|Heqb2]; wp_pures.
      * iApply ("IH" with "Hl").
        iIntros "!> Hl".
        replace (bool_decide (x ∈ left_els)) with x_in_els.
        { iApply "HΦ".
          iApply tree_unfold; iRight.
          eauto 10 with iFrame. }
        apply bool_decide_iff.
        assert (~(key < x)) by lia.
        set_solver.
      * iApply ("IH" with "Hr").
        iIntros "!> Hr".
        replace (bool_decide (x ∈ right_els)) with x_in_els.
        { iApply "HΦ".
          iApply tree_unfold; iRight.
          eauto 10 with iFrame. }
        apply bool_decide_iff.
        assert (key < x) by lia.
        set_solver.
Qed.

End proof.
