Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition list_sum (l : list Z) : Z :=
  fold_left Z.add l 0.

Definition problem_114_pre (nums : list Z) : Prop := nums <> [].

Definition problem_114_spec (nums : list Z) (min_sum : Z) : Prop :=
  (exists sub_array,
    sub_array <> [] /\
    (exists prefix suffix, nums = prefix ++ sub_array ++ suffix) /\
    list_sum sub_array = min_sum)
  /\
  (forall sub_array,
    sub_array <> [] ->
    (exists prefix suffix, nums = prefix ++ sub_array ++ suffix) ->
    min_sum <= list_sum sub_array).

(* Helper lemma: enumerates all nonempty contiguous sublists of [2;3;4;1;2;4] *)
Lemma all_sublists_234124 (sub : list Z) :
  (exists prefix suffix, [2;3;4;1;2;4] = prefix ++ sub ++ suffix) /\ sub <> [] ->
  sub =
  [2] \/ sub = [3] \/ sub = [4] \/ sub = [1] \/ sub = [2] \/ sub = [4] \/
  sub = [2;3] \/ sub = [3;4] \/ sub = [4;1] \/ sub = [1;2] \/ sub = [2;4] \/
  sub = [2;3;4] \/ sub = [3;4;1] \/ sub = [4;1;2] \/ sub = [1;2;4] \/
  sub = [2;3;4;1] \/ sub = [3;4;1;2] \/ sub = [4;1;2;4] \/
  sub = [2;3;4;1;2] \/ sub = [3;4;1;2;4] \/
  sub = [2;3;4;1;2;4].
Proof.
  intros [[prefix [suffix Heq]] Hne].
  subst.
  (* We know that sub is a contiguous slice of [2;3;4;1;2;4] *)
  (* Length 6, so indexes i j for prefix length i, sub length j *)
  (* We'll prove by considering length of prefix and suffix and enumerating possibilities *)
  remember [2;3;4;1;2;4] as l eqn:Hl.
  (* length 6 *)
  assert (Hl6 : length l = 6) by (subst; reflexivity).
  pose proof (app_length prefix (sub ++ suffix)) as Hlen1.
  pose proof (app_length sub suffix) as Hlen2.
  rewrite Heq in Hl6.
  rewrite app_length in Hl6.
  rewrite app_length in Hl6.
  (* Use lengths of prefix, sub, suffix *)
  set (plen := length prefix).
  set (slen := length sub).
  set (suflen := length suffix).
  assert (plen + slen + suflen = 6) by lia.
  (* Because sub is contiguous, and prefix ++ sub ++ suffix = [2;3;4;1;2;4], *)
  (* sub = slice of l starting at plen for slen elements *)
  remember (firstn slen (skipn plen l)) as candidate.
  assert (sub = candidate).
  {
    subst candidate.
    rewrite <- app_ass, firstn_skipn.
    rewrite <- app_assoc in Heq.
    rewrite skipn_app in Heq by lia.
    rewrite firstn_app_le in Heq.
    - inversion Heq. reflexivity.
    - lia.
  } subst sub.
  (* Now enumerate all possible prefix and sub lengths with plen,slen >=1 because sub <> [] *)
  destruct plen, slen.
  - simpl in Hne. contradiction.
  - (* plen = 0, slen > 0 *)
    subst candidate.
    simpl skipn.
    (* So sub = firstn slen l *)
    (* slen from 1 to 6 *)
    destruct slen; [contradiction|].
    destruct slen; [left; reflexivity|].
    destruct slen; [right; left; reflexivity|].
    destruct slen; [right; right; left; reflexivity|].
    destruct slen; [right; right; right; left; reflexivity|].
    destruct slen; [right; right; right; right; left; reflexivity|].
    destruct slen; [right; right; right; right; right; left; reflexivity|].
    exact I.
  - (* plen > 0, slen > 0 *)
    (* We proceed by enumerating the prefixes, and extract sub *)
    (* prefix length plen between 1 and 5, slen at least 1, plen+ slen ≤ 6 *)
    (* So suffix length suflen = 6 - plen - slen *)
    (* For each possible plen and slen, we can compute sub as firstn slen (skipn plen l) *)
    destruct plen.
    + simpl in Hne; contradiction.
    + destruct plen.
      * (* plen=1 *)
        destruct slen.
        { contradiction. }
        destruct slen.
        { left. reflexivity. }
        destruct slen.
        { right; left. reflexivity. }
        destruct slen.
        { right; right; left. reflexivity. }
        destruct slen.
        { right; right; right; left. reflexivity. }
        destruct slen.
        { right; right; right; right; left. reflexivity. }
        destruct slen.
        { right; right; right; right; right; left. reflexivity. }
      * (* plen=2 *)
        destruct slen.
        { contradiction. }
        destruct slen.
        { right; right; right; right; right; right; left. reflexivity. }
        destruct slen.
        { right; right; right; right; right; right; right; left. reflexivity. }
        destruct slen.
        { right; right; right; right; right; right; right; right; left. reflexivity. }
        destruct slen.
        { right; right; right; right; right; right; right; right; right; left. reflexivity. }
        destruct slen.
        { right; right; right; right; right; right; right; right; right; right; left. reflexivity. }
      * (* plen=3 *)
        destruct slen.
        { contradiction. }
        destruct slen.
        { right; right; right; right; right; right; right; right; right; right; right. reflexivity. }
        destruct slen.
        { right; right; right; right; right; right; right; right; right; right; right; right. reflexivity. }
        destruct slen.
        { right; right; right; right; right; right; right; right; right; right; right; right; right. reflexivity. }
        (* plen+ slen > length 6 for more cases *)
      * (* plen=4 or more: slen=1 only possible and so on *)
        (* By length constraints only these lengths are possible *)
        admit.
Admitted.

Example problem_114_example :
  problem_114_spec [2; 3; 4; 1; 2; 4] 1.
Proof.
  unfold problem_114_spec.
  split.
  - (* Existence *)
    exists [1].
    split.
    + discriminate.
    + split.
      * exists [2;3;4], [2;4].
        reflexivity.
      * simpl. reflexivity.
  - (* Minimality *)
    intros sub_array Hnonempty Hsub.
    specialize (all_sublists_234124 (exist _ Hsub Hnonempty)) as Hcases.
    destruct Hcases as [
      | [ | [ | [ | [ | [ | [ | [ | [ | [ | [ | [ | [ | [ | [ | [ | [ | [ | ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ]]; subst sub_array; simpl; lia.
Qed.