inductive vowel
| a : vowel  | A : vowel
| e : vowel  | E : vowel
| u : vowel  | U : vowel

| ae : vowel | aE : vowel
| Ae : vowel | AE : vowel

| au : vowel | aU : vowel
| Au : vowel | AU : vowel

| o : vowel

inductive consonant_hor
| O : consonant_hor
| K : consonant_hor
| G : consonant_hor
| N : consonant_hor
| L : consonant_hor
| R : consonant_hor

inductive consonant_ver
| guttural : consonant_ver
| palatal : consonant_ver
| retroflex : consonant_ver
| dental : consonant_ver
| plosive : consonant_ver

inductive consonant_basic
| grid : consonant_ver → consonant_hor → consonant_basic
| vapour : consonant_hor → consonant_basic
| connector : vowel → vowel → consonant_basic -- this should be quotiented

inductive consonant
| id : consonant_basic → consonant
| crystal : consonant_basic → consonant