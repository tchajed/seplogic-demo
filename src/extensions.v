From DeleteTree Require Import delete_tree.

(** Some extra functions that check that the tree definition makes sense (these
allow you to construct one while delete_tree assumes it's possible) *)

Definition mk_empty_tree: val :=
  λ: <>, ref (InjL #()).

(* this function somewhat arbitrarily adds Some(empty, empty) to the rightmost
child of a tree, expanding it *)
Definition expand_right: val :=
  rec: "expand_right" "x" :=
    match: !"x" with
      InjR "tree" =>
      (let: "right" := Snd "tree" in
       "expand_right" "right")
    | InjL <> => "x" <- SOME (mk_empty_tree #(), mk_empty_tree #())
    end.

Section proof.

Context `{!heapG Σ}.
Implicit Types (t l r:loc).

Theorem wp_mk_empty_tree :
  {{{ emp }}}
    mk_empty_tree #()
  {{{ t, RET #t; tree t }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_rec.
  wp_alloc t as "Ht".
  iApply "HΦ".
  rewrite tree_unfold.
  iExists _; iFrame.
  iLeft; done.
Qed.

Lemma tree_combine_some t l r :
  t ↦ SOMEV (#l, #r) ∗ tree l ∗ tree r ⊢
  tree t.
Proof.
  iIntros "(Ht & Hl & Hr)".
  iApply tree_unfold.
  iExists _; iFrame.
  iRight.
  iExists l, r; iFrame; done.
Qed.

Theorem wp_expand_right t :
  {{{ tree t }}}
    expand_right #t
  {{{ RET #(); tree t }}}.
Proof.
  iLöb as "IH" forall (t).
  iIntros (Φ) "Ht HΦ".
  iDestruct (tree_unfold with "Ht") as (p) "[Hp Hpval]".
  wp_rec.
  wp_load.
  iDestruct "Hpval" as "[-> | Hsubtrees]".
  - wp_pures.
    wp_apply (wp_mk_empty_tree with "[//]").
    iIntros (r) "Hr".
    wp_apply (wp_mk_empty_tree with "[//]").
    iIntros (l) "Hl".
    wp_store.
    iApply "HΦ".
    iApply (tree_combine_some with "[$Hp $Hl $Hr]").
  - iDestruct "Hsubtrees" as (l r) "(-> & Hl & Hr)".
    wp_pures.
    iApply ("IH" with "Hr").
    iIntros "!> Hr".
    iApply "HΦ".
    iApply (tree_combine_some with "[$Hp $Hl $Hr]").
Qed.

End proof.
