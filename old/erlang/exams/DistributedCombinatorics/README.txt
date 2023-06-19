                   M  N
> combinator:start(2, 3).

A  B
1, 1
1, 2
1, 3
2, 1
2, 2
2, 3
3, 1
3, 2
3, 3

---

N = valori possibili
M = ripetizioni

Dobbiamo vedere l'output dal punto di vista delle M (2) colonne, ciascuna di esse può essere rappresentata come una lista:

B: [1, 2, 3, 1, 2, 3, 1, 2, 3] -> N (3) ^ 0 -> 1
A: [1, 1, 1, 2, 2, 2, 3, 3, 3] -> N (3) ^ 1 -> 3

Si nota che le 2 colonne sono composte dalla ripetizione dei 3 (N) possibili elementi (1, 2, 3) seguendo un pattern, la prima colonna ripete ciascun elemento esattamente 1 (3 ^ 0) volta e la seconda 3 (3 ^ 1) volte e ci fossere più colonne si continuerebbe 3 ^ 2, 3 ^ 3...

Notiamo inoltre che le liste sono lunghe esattamente N ^ M = 3 ^ 2 = 9 elementi!

Dovrò quindi spawnare M slaves e ciascuno di essere genererà N ^ M elementi seguendo il pattern descritto in precedenza.
