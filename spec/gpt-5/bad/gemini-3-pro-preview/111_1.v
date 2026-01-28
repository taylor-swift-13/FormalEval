Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

Import ListNotations.

Local Open Scope string_scope.
Local Open Scope list_scope.

Definition space_char : ascii := Ascii.ascii_of_nat 32.

Fixpoint nospace (s : string) : Prop :=
  match s with
  | EmptyString => True
  | String a s' => a <> space_char /\ nospace s'
  end.

Fixpoint join_space (l : list string) : string :=
  match l with
  | nil => EmptyString
  | x :: nil => x
  | x :: xs => String.append x (String.append (String space_char EmptyString) (join_space xs))
  end.

Fixpoint occ (x : string) (l : list string) : nat :=
  match l with
  | nil => 0
  | y :: ys => if string_dec y x then S (occ x ys) else occ x ys
  end.

Definition histogram_spec (test : string) (ans : list (string * nat)) : Prop :=
  (test = EmptyString /\ ans = nil) \/
  (test <> EmptyString /\
   exists tokens : list string,
     Forall nospace tokens /\
     test = join_space tokens /\
     exists m : nat,
       exists s0 : string,
         s0 <> EmptyString /\ In s0 tokens /\ m = occ s0 tokens /\
         (forall s : string, s <> EmptyString /\ In s tokens -> occ s tokens <= m) /\
         NoDup (map (@fst string nat) ans) /\
         (forall s n, In (s, n) ans -> n = m /\ s <> EmptyString /\ occ s tokens = m) /\
         (forall s : string, s <> EmptyString /\ occ s tokens = m -> In (s, m) ans)).

Example test_histogram : histogram_spec "a b b a" [("a", 2); ("b", 2)].
Proof.
  unfold histogram_spec.
  right.
  split.
  - intro H. discriminate.
  - exists ["a"; "b"; "b"; "a"].
    split.
    + (* Forall nospace tokens *)
      repeat constructor.
      all: simpl; split; try (intro H; inversion H); try exact I.
    + split.
      * (* test = join_space tokens *)
        reflexivity.
      * (* exists m *)
        exists 2.
        (* exists s0 *)
        exists "a".
        split. { intro H; discriminate. }
        split. { simpl; left; reflexivity. }
        split. { reflexivity. }
        split.
        { (* forall s : string, s <> EmptyString /\ In s tokens -> occ s tokens <= m *)
          intros s [Hneq Hin].
          simpl in *.
          destruct (string_dec "a" s) as [Heqa|Hneqa];
          destruct (string_dec "b" s) as [Heqb|Hneqb]; subst; try lia.
          - (* s is neither "a" nor "b" *)
            destruct Hin as [H|Hin]; try congruence.
            destruct Hin as [H|Hin]; try congruence.
            destruct Hin as [H|Hin]; try congruence.
            destruct Hin as [H|Hin]; try congruence.
            contradiction.
        }
        split.
        { (* NoDup (map fst ans) *)
          simpl. constructor.
          - intro H. destruct H as [H|H]; try discriminate; contradiction.
          - constructor; [intro H; contradiction | constructor].
        }
        split.
        { (* forall s n, In (s, n) ans -> ... *)
          intros s n Hin.
          simpl in Hin.
          destruct Hin as [H | [H | H]].
          - inversion H; subst. simpl. repeat split; try discriminate; auto.
          - inversion H; subst. simpl. repeat split; try discriminate; auto.
          - contradiction.
        }
        { (* forall s, ... occ s tokens = m -> In (s, m) ans *)
          intros s [Hneq Hocc].
          simpl in Hocc.
          destruct (string_dec "a" s); destruct (string_dec "b" s); subst.
          - left; reflexivity.
          - left; reflexivity.
          - right; left; reflexivity.
          - discriminate.
        }
Qed.