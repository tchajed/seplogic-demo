From iris.heap_lang Require Import proofmode notation.

Set Warnings "-convert_concl_no_check".
Set Default Goal Selector "!".

(** * deletetree from the Separation Logic CACM paper by O'Hearn *)

(** A tree will be a pointer to either None (represented InjL #()) or Some(l,r)
(represented InjR (l, r)), where l and r are themselves trees. *)

(** delete_tree is a version of the deletetree function from the paper, written
in an OCaml-like language rather than the C code in the paper. *)
Definition delete_tree: val :=
  (* the rec: here starts a recursive function *)
  rec: "delete_tree" "x" :=
    (* !"x" deferences the variable x (variables need to be quoted) *)
    match: !"x" with
      InjR "tree" =>
      (* if this tree has children, delete them first. Recall the tree is just a
      tuple of the left and right child tree pointers. *)
      (let: "left" := Fst "tree" in
       let: "right" := Snd "tree" in
       "delete_tree" "left";;
       "delete_tree" "right";;
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

Set Default Proof Using "Type".
Context `{!heapG Σ}.
Implicit Types (t l r:loc).

(* You can ignore some magic that creates the recursive tree predicate... *)

Definition tree_pre (tree: loc -d> iPropO Σ): loc -d> iPropO Σ :=
  (λ t, ∃ p, t ↦ p ∗
        (⌜p = InjLV #()⌝ ∨ ∃ l r, ⌜p = InjRV (#l, #r)⌝ ∗ ▷ tree l ∗ ▷ tree r))%I.

Local Instance tree_pre_contractive : Contractive tree_pre.
Proof.
  rewrite /tree_pre=> n tree tree' Htree t.
  repeat (f_contractive || f_equiv); apply Htree.
Qed.

Definition tree : loc → iProp Σ := fixpoint tree_pre.

(** Following the fixpoint magic above, the definition [tree] ends up being the
recursive definition we expect (the ⊣⊢ means "equivalent"): *)
Theorem tree_unfold t :
  tree t ⊣⊢
  ∃ p, t ↦ p ∗
       (⌜p = InjLV #()⌝ ∨ ∃ l r, ⌜p = InjRV (#l, #r)⌝ ∗ ▷ tree l ∗ ▷ tree r).
Proof. apply (fixpoint_unfold tree_pre). Qed.

Theorem wp_delete_tree t :
  {{{ tree t }}}
    delete_tree #t
  {{{ RET #(); emp }}}.
Proof.
  (* this is how we start a recursive proof: *)
  iLöb as "IH" forall (t).
  iIntros (Φ) "Ht HΦ".
  (* What we get from iLöb is an assumption that delete_tree follows the
  specification. How is that possible? Couldn't we just use it right away and
  not have to any work? Indeed! That's why this assumption has the ▷ (pronounced
  "later") in front. ▷ P means we only get to know that P holds after one "step"
  within our function. This is enough to handle all the recursive calls but
  can't be used to just dismiss the whole proof (otherwise proofs would be easy
  but not very meaningful) *)

  (* first, we need to destruct [tree] to learn the basic structure: a tree is
  always a pointer, either to nothing or to a pair of children. *)
  iDestruct (tree_unfold with "Ht") as (p) "[Hp Hpval]".
  wp_rec.
  wp_load.
  (* the main structure of the tree is determined by Hpval, which is a
  disjunction, so let's do a case-split and handle both possibilities (since
  that's what the code will do, too) *)
  iDestruct "Hpval" as "[-> | Hsubtrees]".
  - wp_pures.
    (* in the case where the tree is None we just free the root pointer *)
    wp_free.
    iApply "HΦ"; done.
  - (* in the other case we need to further destruct [tree] to get out the left
    and right subtrees (both their root pointers and the corresponding [tree]
    predicates) *)
    iDestruct "Hsubtrees" as (l r) "(-> & Hl & Hr)".
    wp_pures.
    wp_apply ("IH" with "Hl"); iIntros "_"; wp_pures.
    wp_apply ("IH" with "Hr"); iIntros "_"; wp_pures.
    wp_free.
    iApply "HΦ"; done.
Qed.

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
