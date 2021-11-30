From demo Require Import simplified_iris delete_tree.
From iris.heap_lang Require Import lib.par.

Definition delete_tree_par: val :=
  rec: "delete_tree" "x" :=
    match: !"x" with
      InjR "tree" =>
      (* this time, delete in parallel *)
      (let: "left" := Fst "tree" in
       let: "right" := Snd "tree" in
       ("delete_tree" "left" ||| "delete_tree" "right");;
      (* then free the root pointer *)
      Free "x")
    | InjL <> =>
      (* the way we've represented trees, even an empty tree is a pointer to a
      None, so free that, too *)
      Free "x"
    end.

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

Context `{!heapGS Σ} `{!spawnG Σ}.
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
  iLeft; done.
Qed.

Lemma tree_combine_some t l r :
  t ↦ SOMEV (#l, #r) ∗ tree l ∗ tree r ⊢
  tree t.
Proof.
  iIntros "(Ht & Hl & Hr)".
  iApply tree_unfold.
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
  iDestruct (tree_unfold with "Ht") as "[Hp|Hp]"; wp_rec.
  - wp_load; wp_pures.
    wp_apply (wp_mk_empty_tree with "[//]").
    iIntros (r) "Hr".
    wp_apply (wp_mk_empty_tree with "[//]").
    iIntros (l) "Hl".
    wp_store.
    iApply "HΦ".
    iApply (tree_combine_some with "[$Hp $Hl $Hr]").
  - iDestruct "Hp" as (l r) "(Hp & Hleft & Hright)".
    wp_load; wp_pures.
    iApply ("IH" with "Hright").
    iIntros "!> Hright".
    iApply "HΦ".
    iApply (tree_combine_some with "[$Hp $Hleft $Hright]").
Qed.

Theorem wp_delete_tree_par t :
  {{{ tree t }}}
    delete_tree_par #t
  {{{ RET #(); emp }}}.
Proof using All.
  iLöb as "IH" forall (t).
  iIntros (Φ) "Ht HΦ".
  iDestruct (tree_unfold with "Ht") as "[Ht|Ht]"; wp_rec.
  - wp_load; wp_pures.
    wp_free.
    iApply "HΦ"; auto.
  - iDestruct "Ht" as (l r) "(Ht & Hl & Hr)".
    wp_load; wp_pures.
    wp_apply (wp_par (λ _, emp)%I (λ _, emp)%I with "[Hl] [Hr]").
    + wp_apply ("IH" with "Hl"); iIntros "_".
      done.
    + wp_apply ("IH" with "Hr"); iIntros "_".
      done.
    + iIntros (??) "_ !>".
      wp_pures.
      wp_free.
      iApply "HΦ"; auto.
Qed.

End proof.
