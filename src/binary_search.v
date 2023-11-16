From demo Require Import simplified_iris.
From stdpp Require Import list.

(** Extension of the deletetree demo from the paper where we prove functional
correctness of some binary search tree operations. The definition of a [tree]
will now take an additional parameter giving its abstract value: in this case,
that is a set of integers logically stored in the tree. *)

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
Proof. solve_contractive. Qed.

Definition tree : loc → gset Z → iProp Σ := fixpoint tree_pre.

(** More complicated than the equivalent in delete_tree.v, but only because we
need to capture the memory layout, how the abstract state is encoded, and also
the binary search invariant. *)
Theorem tree_unfold t els :
  tree t els ⊣⊢
  (⌜els = ∅⌝ ∧ t ↦ NONEV) ∨
    (∃ left_els right_els (key: Z) l r,
        ⌜els = {[key]} ∪ left_els ∪ right_els⌝ ∗
                 (* "left_els < key" *)
        ⌜∀ e, e ∈ left_els → e < key⌝ ∗
                 (* "key < right_els" *)
        ⌜∀ e, e ∈ right_els → key < e⌝ ∗
        t ↦ SOMEV (#key, (#l, #r)) ∗
        ▷ tree l left_els ∗ ▷ tree r right_els).
Proof. apply (fixpoint_unfold tree_pre). Qed.

Lemma tree_empty t :
  t ↦ NONEV ⊢ tree t ∅.
Proof.
  iIntros "Ht".
  iApply tree_unfold; iLeft; auto.
Qed.

Lemma singleton_tree_from_empty (x : Z) t r l :
  t ↦ SOMEV (#x, (#l, #r)) ∗
    l ↦ NONEV ∗
    r ↦ NONEV ⊢
  tree t ({[x]} ∪ ∅).
Proof.
  iIntros "(Ht & Hl & Hr)".
  rewrite tree_unfold.
  iRight.
  iExists ∅, ∅, _, _, _.
  iFrame.
  iSplit; first by (iPureIntro; set_solver).
  iSplit; first by (iPureIntro; set_solver).
  iSplit; first by (iPureIntro; set_solver).
  rewrite -!tree_empty.
  iFrame.
Qed.

Lemma tree_insert_left (x : Z) t (left_els right_els : gset Z) (key : Z) l r :
  (∀ e : Z, e ∈ left_els → e < key)
  → (∀ e : Z, e ∈ right_els → key < e)
  → x < key
  → t ↦ SOMEV (#key, (#l, #r)) ∗
      tree l ({[x]} ∪ left_els) ∗
      tree r right_els ⊢
  tree t ({[x]} ∪ ({[key]} ∪ left_els ∪ right_els)).
Proof.
  intros Hleft Hright Heqb2.
  iIntros "(Ht & Hl & Hr)".
  iApply tree_unfold; iRight.
  iExists ({[x]} ∪ left_els), right_els, _, _, _; iFrame.
  iPureIntro.
  (* [set_solver] does a lot of work here for us *)
  set_solver.
Qed.

Lemma tree_insert_right t (left_els right_els : gset Z)
  (x key : Z) l r :
  (∀ e : Z, e ∈ left_els → e < key)
  → (∀ e : Z, e ∈ right_els → key < e)
  → key < x
  → t ↦ SOMEV (#key, (#l, #r)) ∗
      tree l left_els ∗
      tree r ({[x]} ∪ right_els) ⊢
  tree t ({[x]} ∪ ({[key]} ∪ left_els ∪ right_els)).
Proof.
  intros Hleft Hright Heqb2.
  iIntros "(Ht & Hl & Hr)".
  iApply tree_unfold; iRight.
  iExists left_els, ({[x]} ∪ right_els), _, _, _; iFrame.
  iPureIntro.
  set_solver.
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
    (* this is just "symbolic execution", directed by the program syntax *)
    wp_load; wp_pures.
    wp_alloc r.
    wp_alloc l.
    wp_store.
    iApply "HΦ".
    iModIntro.

    (* here we build a singleton [tree] predicate out of points-to facts *)
    iApply (singleton_tree_from_empty with "[$]").
  - iDestruct "Ht" as (????? -> Hleft Hright) "(Ht&Hl&Hr)".
    wp_load; wp_pures.
    case_bool_decide as Heqb; wp_pures.
    + iModIntro.
      inversion Heqb; subst.
      iApply "HΦ".

      (* another [tree] separation logic theorem (no code involved) *)
      rewrite !assoc_L.
      replace {[key; key]} with ({[key]}: gset Z) by set_solver.
      iApply tree_unfold; iRight.
      iExists left_els, right_els, _, _, _; iFrame.
      iPureIntro.
      split_and!; set_solver.
    + assert (x ≠ key) by (intros ->; auto).
      case_bool_decide as Heqb2; wp_pures.
      * iApply ("IH" with "Hl").
        iIntros "!> Hl".
        iApply "HΦ".

        iApply (tree_insert_left with "[$Ht $Hl $Hr]"); auto.
      * iApply ("IH" with "Hr").
        iIntros "!> Hr".
        iApply "HΦ".

        assert (key < x) by lia.
        iApply (tree_insert_right with "[$Ht $Hl $Hr]"); auto.
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
    case_bool_decide as Heqb; wp_pures.
    + inversion Heqb; subst.
      replace x_in_els with true.
      { iApply "HΦ".
        (* this is a little silly: we haven't modified anything but we have to
        reconstruct the [tree] predicate *)
        iApply tree_unfold; iRight.
        eauto 10 with iFrame. }
      rewrite /x_in_els.
      apply symmetry, bool_decide_eq_true.
      set_solver.
    + assert (x ≠ key) by (intros ->; auto).
      case_bool_decide as Heqb2; wp_pures.
      * iApply ("IH" with "Hl").
        iIntros "!> Hl".
        replace (bool_decide (x ∈ left_els)) with x_in_els.
        { iApply "HΦ".
          iApply tree_unfold; iRight.
          eauto 10 with iFrame. }
        apply bool_decide_ext.
        assert (~(key < x)) by lia.
        set_solver.
      * iApply ("IH" with "Hr").
        iIntros "!> Hr".
        replace (bool_decide (x ∈ right_els)) with x_in_els.
        { iApply "HΦ".
          iApply tree_unfold; iRight.
          eauto 10 with iFrame. }
        apply bool_decide_ext.
        assert (key < x) by lia.
        set_solver.
Qed.

End proof.
