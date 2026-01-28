Example vowels_count_abcde_example : problem_64_spec "abcde" 2.
Proof.
  unfold problem_64_spec.
  apply (vcr_vowel "a"%char "bcde" 1).
  - constructor.
  - apply (vcr_other "b"%char "cde" 1).
    + intro H; inversion H.
    + intro H; destruct H; inversion H.
    + apply (vcr_other "c"%char "de" 1).
      * intro H; inversion H.
      * intro H; destruct H; inversion H.
      * apply (vcr_vowel "d"%char "e" 0).
        { constructor. }
        { apply (vcr_vowel "e"%char "" 0).
          - constructor.
          - constructor.
        }
Qed.