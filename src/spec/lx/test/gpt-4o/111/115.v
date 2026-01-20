Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition histogram_spec (letters : list ascii) (res : list (ascii * nat)) : Prop :=
  let unique_letters := nodup ascii_dec letters in
  match unique_letters with
  | [] => res = []
  | _ :: _ =>
    let count_char (c : ascii) := count_occ ascii_dec letters c in
    let counts := map count_char unique_letters in
    let max_count := fold_right max 0 counts in
    (forall (p : ascii * nat), In p res ->
      let (c, n) := p in
      n = max_count /\ count_char c = max_count) /\
    (forall c, In c unique_letters ->
      count_char c = max_count ->
      In (c, max_count) res)
  end.

Example histogram_test :
  histogram_spec ["h"%char]
                 [("h"%char, 1)].
Proof.
  unfold histogram_spec.
  simpl.
  split.
  - intros p Hp.
    destruct Hp as [Hp | []]; subst; simpl; split; reflexivity.
  - intros c Hc Hcount.
    simpl in Hc.
    destruct Hc as [Hc | []]; subst; simpl; auto.
Qed.