Require Import String Ascii Arith Bool Lia.

Definition IsLow (c : ascii) : Prop :=
  (nat_of_ascii "a" <= nat_of_ascii c)%nat /\
  (nat_of_ascii c <= nat_of_ascii "z")%nat.

Definition IsUp (c : ascii) : Prop :=
  (nat_of_ascii "A" <= nat_of_ascii c)%nat /\
  (nat_of_ascii c <= nat_of_ascii "Z")%nat.

Definition Upper (c : ascii) : ascii :=
  if (nat_of_ascii "a" <=? nat_of_ascii c)%nat &&
     (nat_of_ascii c <=? nat_of_ascii "z")%nat
  then ascii_of_nat (nat_of_ascii c - 32)
  else c.

Definition Lower (c : ascii) : ascii :=
  if (nat_of_ascii "A" <=? nat_of_ascii c)%nat &&
     (nat_of_ascii c <=? nat_of_ascii "Z")%nat
  then ascii_of_nat (nat_of_ascii c + 32)
  else c.

Definition problem_27_pre (input : string) : Prop := True.

Definition problem_27_spec (input output : string) : Prop :=
  String.length input = String.length output /\
  (forall (i : nat) (c : ascii),
    i < String.length input ->
    String.get i input = Some c ->
    (IsLow c -> String.get i output = Some (Upper c)) /\
    (IsUp c -> String.get i output = Some (Lower c)) /\
    (~IsLow c /\ ~IsUp c -> String.get i output = Some c)).

Fixpoint flip_case (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' =>
    let c' := if (nat_of_ascii "a" <=? nat_of_ascii c)%nat &&
                 (nat_of_ascii c <=? nat_of_ascii "z")%nat
              then ascii_of_nat (nat_of_ascii c - 32)
              else if (nat_of_ascii "A" <=? nat_of_ascii c)%nat &&
                       (nat_of_ascii c <=? nat_of_ascii "Z")%nat
                   then ascii_of_nat (nat_of_ascii c + 32)
                   else c
    in String c' (flip_case s')
  end.

Example test_flip_case_toggle_me :
  problem_27_spec "toggle me" (flip_case "toggle me").
Proof.
  unfold problem_27_spec.
  split.
  - simpl. reflexivity.
  - intros i c Hlt Hget.
    revert i c Hlt Hget.
    (* We do induction on the input string "toggle me" *)
    Remember "toggle me" as s eqn:Hs.
    Remember (flip_case s) as fflip eqn:Hf.
    assert (Hs_len: String.length s = 9) by (subst; reflexivity).
    intros i c Hlt Hget.
    subst s fflip.
    (* We do a general induction on n: length of the string and process index i *)
    induction 9 as [|n IHn] in i, c, Hlt, Hget |- *.
    + lia.
    + destruct i as [|i'].
      * simpl in Hget. 
        simpl.
        (* head char of "toggle me" is "t" *)
        unfold flip_case.
        simpl.
        rewrite String.ascii_dec_eqb_refl.
        (* c = "t" *)
        simpl in Hget.
        inversion Hget; subst c.
        split.
        -- (* IsLow "t" *) unfold IsLow.
           simpl.
           split; unfold nat_of_ascii.
           + (* nat_of_ascii "a" <= nat_of_ascii "t" *) simpl. lia.
           + (* nat_of_ascii "t" <= nat_of_ascii "z" *) simpl. lia.
        -- split.
           ++ intro Hup. destruct Hup as [H1 H2].
              simpl in Hup. lia.
           ++ intro Hnor. destruct Hnor as [Hn1 Hn2].
              simpl.
              rewrite Bool.andb_false_r.
              reflexivity.
      * simpl.
        simpl in Hget.
        (* Decompose the string *)
        assert (Hi: i' < n) by lia.
        specialize (IHn i' c Hi Hget).
        (* The induction hypothesis gives the prop for the tail *)
        destruct IHn as [Hl [Hu [Hne Hc]]].
        split; [exact Hl|].
        split; [exact Hu|].
        exact Hne.
Qed.