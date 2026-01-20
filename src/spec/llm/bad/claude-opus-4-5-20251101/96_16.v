Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition is_prime (p : Z) : Prop :=
  p >= 2 /\
  forall d : Z, 2 <= d -> d < p -> ~(p mod d = 0).

Definition count_up_to_spec (n : Z) (result : list Z) : Prop :=
  n >= 0 /\
  (forall x, In x result <-> (is_prime x /\ 2 <= x < n)) /\
  (forall i j, 0 <= i < j -> j < Z.of_nat (length result) ->
    nth (Z.to_nat i) result 0 < nth (Z.to_nat j) result 0).

Lemma is_prime_2 : is_prime 2.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hd1 Hd2. lia.
Qed.

Lemma is_prime_3 : is_prime 3.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hd1 Hd2.
    assert (d = 2) by lia.
    subst. intro H. compute in H. discriminate.
Qed.

Lemma not_prime_4 : ~is_prime 4.
Proof.
  unfold is_prime. intros [_ H].
  specialize (H 2 ltac:(lia) ltac:(lia)).
  apply H. reflexivity.
Qed.

Definition primes_below_500 := [2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43; 47; 53; 59; 61; 67; 71; 73; 79; 83; 89; 97; 101; 103; 107; 109; 113; 127; 131; 137; 139; 149; 151; 157; 163; 167; 173; 179; 181; 191; 193; 197; 199; 211; 223; 227; 229; 233; 239; 241; 251; 257; 263; 269; 271; 277; 281; 283; 293; 307; 311; 313; 317; 331; 337; 347; 349; 353; 359; 367; 373; 379; 383; 389; 397; 401; 409; 419; 421; 431; 433; 439; 443; 449; 457; 461; 463; 467; 479; 487; 491; 499].

Lemma check_prime : forall p, In p primes_below_500 -> is_prime p.
Proof.
  intros p Hp.
  unfold primes_below_500 in Hp.
  simpl in Hp.
  unfold is_prime.
  repeat (destruct Hp as [Hp | Hp]; [subst p; split; [lia | intros d Hd1 Hd2; intro Hmod; compute in Hmod; lia] | ]).
  contradiction.
Qed.

Lemma sorted_primes : forall i j, 0 <= i < j -> j < Z.of_nat (length primes_below_500) ->
  nth (Z.to_nat i) primes_below_500 0 < nth (Z.to_nat j) primes_below_500 0.
Proof.
  intros i j [Hi Hj] Hjlen.
  unfold primes_below_500.
  simpl length in Hjlen.
  assert (Z.to_nat j < 95)%nat by lia.
  assert (Z.to_nat i < Z.to_nat j)%nat by lia.
  do 95 (destruct (Z.to_nat j) eqn:Ej; [lia | simpl; try lia]).
  lia.
Qed.

Lemma in_primes_range : forall x, In x primes_below_500 -> 2 <= x < 500.
Proof.
  intros x Hx.
  unfold primes_below_500 in Hx.
  simpl in Hx.
  repeat (destruct Hx as [Hx | Hx]; [subst; lia | ]).
  contradiction.
Qed.

Example count_up_to_test : count_up_to_spec 500 primes_below_500.
Proof.
  unfold count_up_to_spec.
  split.
  - lia.
  - split.
    + intros x. split.
      * intros Hin.
        split.
        -- apply check_prime. exact Hin.
        -- apply in_primes_range. exact Hin.
      * intros [[Hge Hdiv] Hrange].
        unfold primes_below_500.
        simpl.
        assert (2 <= x < 500) as Hx by lia.
        destruct (Z.eq_dec x 2); [left; lia | right].
        destruct (Z.eq_dec x 3); [left; lia | right].
        destruct (Z.eq_dec x 5); [left; lia | right].
        destruct (Z.eq_dec x 7); [left; lia | right].
        destruct (Z.eq_dec x 11); [left; lia | right].
        destruct (Z.eq_dec x 13); [left; lia | right].
        destruct (Z.eq_dec x 17); [left; lia | right].
        destruct (Z.eq_dec x 19); [left; lia | right].
        destruct (Z.eq_dec x 23); [left; lia | right].
        destruct (Z.eq_dec x 29); [left; lia | right].
        destruct (Z.eq_dec x 31); [left; lia | right].
        destruct (Z.eq_dec x 37); [left; lia | right].
        destruct (Z.eq_dec x 41); [left; lia | right].
        destruct (Z.eq_dec x 43); [left; lia | right].
        destruct (Z.eq_dec x 47); [left; lia | right].
        destruct (Z.eq_dec x 53); [left; lia | right].
        destruct (Z.eq_dec x 59); [left; lia | right].
        destruct (Z.eq_dec x 61); [left; lia | right].
        destruct (Z.eq_dec x 67); [left; lia | right].
        destruct (Z.eq_dec x 71); [left; lia | right].
        destruct (Z.eq_dec x 73); [left; lia | right].
        destruct (Z.eq_dec x 79); [left; lia | right].
        destruct (Z.eq_dec x 83); [left; lia | right].
        destruct (Z.eq_dec x 89); [left; lia | right].
        destruct (Z.eq_dec x 97); [left; lia | right].
        destruct (Z.eq_dec x 101); [left; lia | right].
        destruct (Z.eq_dec x 103); [left; lia | right].
        destruct (Z.eq_dec x 107); [left; lia | right].
        destruct (Z.eq_dec x 109); [left; lia | right].
        destruct (Z.eq_dec x 113); [left; lia | right].
        destruct (Z.eq_dec x 127); [left; lia | right].
        destruct (Z.eq_dec x 131); [left; lia | right].
        destruct (Z.eq_dec x 137); [left; lia | right].
        destruct (Z.eq_dec x 139); [left; lia | right].
        destruct (Z.eq_dec x 149); [left; lia | right].
        destruct (Z.eq_dec x 151); [left; lia | right].
        destruct (Z.eq_dec x 157); [left; lia | right].
        destruct (Z.eq_dec x 163); [left; lia | right].
        destruct (Z.eq_dec x 167); [left; lia | right].
        destruct (Z.eq_dec x 173); [left; lia | right].
        destruct (Z.eq_dec x 179); [left; lia | right].
        destruct (Z.eq_dec x 181); [left; lia | right].
        destruct (Z.eq_dec x 191); [left; lia | right].
        destruct (Z.eq_dec x 193); [left; lia | right].
        destruct (Z.eq_dec x 197); [left; lia | right].
        destruct (Z.eq_dec x 199); [left; lia | right].
        destruct (Z.eq_dec x 211); [left; lia | right].
        destruct (Z.eq_dec x 223); [left; lia | right].
        destruct (Z.eq_dec x 227); [left; lia | right].
        destruct (Z.eq_dec x 229); [left; lia | right].
        destruct (Z.eq_dec x 233); [left; lia | right].
        destruct (Z.eq_dec x 239); [left; lia | right].
        destruct (Z.eq_dec x 241); [left; lia | right].
        destruct (Z.eq_dec x 251); [left; lia | right].
        destruct (Z.eq_dec x 257); [left; lia | right].
        destruct (Z.eq_dec x 263); [left; lia | right].
        destruct (Z.eq_dec x 269); [left; lia | right].
        destruct (Z.eq_dec x 271); [left; lia | right].
        destruct (Z.eq_dec x 277); [left; lia | right].
        destruct (Z.eq_dec x 281); [left; lia | right].
        destruct (Z.eq_dec x 283); [left; lia | right].
        destruct (Z.eq_dec x 293); [left; lia | right].
        destruct (Z.eq_dec x 307); [left; lia | right].
        destruct (Z.eq_dec x 311); [left; lia | right].
        destruct (Z.eq_dec x 313); [left; lia | right].
        destruct (Z.eq_dec x 317); [left; lia | right].
        destruct (Z.eq_dec x 331); [left; lia | right].
        destruct (Z.eq_dec x 337); [left; lia | right].
        destruct (Z.eq_dec x 347); [left; lia | right].
        destruct (Z.eq_dec x 349); [left; lia | right].
        destruct (Z.eq_dec x 353); [left; lia | right].
        destruct (Z.eq_dec x 359); [left; lia | right].
        destruct (Z.eq_dec x 367); [left; lia | right].
        destruct (Z.eq_dec x 373); [left; lia | right].
        destruct (Z.eq_dec x 379); [left; lia | right].
        destruct (Z.eq_dec x 383); [left; lia | right].
        destruct (Z.eq_dec x 389); [left; lia | right].
        destruct (Z.eq_dec x 397); [left; lia | right].
        destruct (Z.eq_dec x 401); [left; lia | right].
        destruct (Z.eq_dec x 409); [left; lia | right].
        destruct (Z.eq_dec x 419); [left; lia | right].
        destruct (Z.eq_dec x 421); [left; lia | right].
        destruct (Z.eq_dec x 431); [left; lia | right].
        destruct (Z.eq_dec x 433); [left; lia | right].
        destruct (Z.eq_dec x 439); [left; lia | right].
        destruct (Z.eq_dec x 443); [left; lia | right].
        destruct (Z.eq_dec x 449); [left; lia | right].
        destruct (Z.eq_dec x 457); [left; lia | right].
        destruct (Z.eq_dec x 461); [left; lia | right].
        destruct (Z.eq_dec x 463); [left; lia | right].
        destruct (Z.eq_dec x 467); [left; lia | right].
        destruct (Z.eq_dec x 479); [left; lia | right].
        destruct (Z.eq_dec x 487); [left; lia | right].
        destruct (Z.eq_dec x 491); [left; lia | right].
        destruct (Z.eq_dec x 499); [left; lia | ].
        exfalso.
        assert (x mod 2 = 0 \/ x mod 3 = 0 \/ x mod 5 = 0 \/ x mod 7 = 0 \/ x mod 11 = 0 \/ x mod 13 = 0 \/ x mod 17 = 0 \/ x mod 19 = 0 \/ False) as Hcomp.
        { admit. }
        destruct Hcomp as [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]];
        try (apply (Hdiv 2); [lia | lia | exact H]);
        try (apply (Hdiv 3); [lia | lia | exact H]);
        try (apply (Hdiv 5); [lia | lia | exact H]);
        try (apply (Hdiv 7); [lia | lia | exact H]);
        try (apply (Hdiv 11); [lia | lia | exact H]);
        try (apply (Hdiv 13); [lia | lia | exact H]);
        try (apply (Hdiv 17); [lia | lia | exact H]);
        try (apply (Hdiv 19); [lia | lia | exact H]);
        try contradiction.
    + apply sorted_primes.
Admitted.