### Scopo del progetto

Lo scopo del nostro progetto è quello di realizzare un emulatore
CHIP-8 e S-CHIP in grado di funzionare su un microcontrollore STM32.

### CHIP-8 (1)

**Ma esattamente cos'è CHIP-8?**

CHIP-8 è un linguaggio di programmazione creato a metà degli anni '70
per semplificare lo sviluppo di videogiochi per microcomputer a 8 bit.

Questo linguaggio viene interpretato da una macchina virtuale, che è
stata estesa più volte nel corso degli anni, in particolare citiamo le
due estensioni principali che sono S-CHIP e XO-CHIP.

S-CHIP è stata pensata inizialmente per le calcolatrici HP 48 e risale
ai primi anni '90.

S-CHIP raddoppia la dimensione dello schermo e aggiunge delle
istruzioni come ad esempio lo scroll orizzontale.

XO-CHIP invece è un'estensione più moderna ed è pensata per "portare"
CHIP-8 su desktop moderni, ad esempio la memoria dell'emulatore passa
da 4 KB a 64 KB.

**Quali videogiochi esistono per CHIP-8?**

Beh, molti videogiochi storici sono stati riscritti in CHIP-8, in
particolare citiamo Pong, Space Invaders e Tetris.

### CHIP-8 (2)

Allora, CHIP-8 è un po' una nicchia ma ha una sua community online,
infatti ogni anno viene tenuta una gamejam dove i partecipanti
sviluppano un loro videogioco.

Inoltre, CHIP-8 è stato "portato" su un elevato numero di piattaforme
tra cui le calcolatrici grafiche HP 48, che tengo però a far notare,
sono più potenti della nostra scheda, hanno circa il doppio della
memoria.

E anche Emacs, il famoso editor di testo

### Interprete CHIP-8 (1)

Allora, ci tengo a fare una precisazione, ci riferiremo alla macchina
virtuale che interpreta programmi CHIP-8 con "interprete", mentre con
"emulatore" ci riferiamo all'interprete assieme ai gestori per le
periferiche audio, video, eccetera.

La macchina virtuale ha un'architettura basata su registri e possiede
4 KB di memoria, 16 registri general purpose, un registro per gli
indirizzi di memoria, uno stack per le chiamate a subroutine, uno
stack pointer e un program counter.

### Interprete CHIP-8 (2)

Proprio come un processore reale, l'interprete effettua il fetch
dell'istruzione puntata dal program counter in memoria, la decodifica
e la esegue.

Il cosiddetto Fetch-Decode-Execute cycle.

Sono supportate 45 istruzioni diverse, ciascuna delle quali è
rappresentata da un opcode contenente al suo interno anche eventuali
parametri.

### Interprete CHIP-8 (3)

Abbiamo scritto il programma in modo da essere altamente portabile.

In particolare l'abbiamo scritto in C99, non ha I/O ed è freestanding,
ovvero non dipende dalla libreria standard del C.

Per rimuovere questa dipendenza è stato necessario includere memset e
memcpy da libgcc.

E abbiamo gestito le asserzioni con una macro che verifica una
condizione, e se questa è falsa dereferenziamo un puntatore a NULL
crashando così il programma.

Infine abbiamo dovuto includere anche una funzione ad hoc per la
generazione di numeri casuali.

Abbiamo testato l'interprete manualmente utilizzando una port su
desktop sviluppata con SDL2 e in seguito abbiamo sottoposto
l'interprete ad un'apposita test suite per verificare il comportamento
corretto di ogni opcode.

### Gestione del timing

Uno dei problemi principali durante lo sviluppo di un emulatore è la
gestione del timing, in particolare è necessario limitare la
"velocità" dell'interprete bloccando temporaneamente la sua
esecuzione.

Durante lo sviluppo abbiamo testato due soluzioni diverse.

Inizialmente gestivamo una singola istruzione per ciclo di esecuzione,
il ritardo in questo caso era variabile e dipendeva dalla "velocità"
dell'emulatore.

Maggior la velocità, minore il ritardo.

Questa soluzione però aveva un problema, ovvero chiamava una funzione
simil-sleep per un periodo troppo breve, e questo genere di funzione
non offre una precisione simile.

Per questo motivo abbiamo deciso di gestire più istruzioni per ciclo
di esecuzione.

Il ritardo adesso è costante a 16 millisecondi in modo tale da
ottenere 60 FPS precisi.

E a questo punto è il numero di istruzioni eseguite a dipendere dalla
"velocità" dell'emulatore.

### Ottimizzazioni

L'ottimizzazione principale è legata allo schermo.

Lo schermo può essere visto come una matrice di 128x64 pixel
monocromi.

C'è un problema però, questa rappresentazione occupa 8 KB di memoria e
noi abbiamo a disposizione solo 16 KB di SRAM.

La soluzione è stata quella di rappresentare lo schermo come un array
unidimensionale di 1024 byte, dove ciascun pixel viene rappresentato
da un singolo bit, anziché da un singolo byte.

Otteniamo così un risparmio di spazio pari a ben l'87.5%!

Questa ottimizzazione ha aggiunto però un livello di indirezione:
ovvero una coordinata sulla matrice deve essere mappata ad una
coordinata in "memoria".

### Comportamenti ambigui

Gli emulatori CHIP-8 hanno sviluppato comportamenti ambigui nel corso
degli anni.

Questi cosiddetti "quirk" variano in base alle piattaforme per cui è
stato sviluppato l'interprete, ad esempio gli interpreti per
calcolatrici HP 48 gestiscono le istruzioni di SHIFT in modo un po'
diverso.

Questi comportamenti ambigui si propagano fino ai programmatori CHIP-8
che si appoggiano a quest'ultimi e scrivono videogiochi che non sono
del tutto retrocompatibili.

Per evitare la frammentazione bisogna quindi supportare le piattaforme
principali e i loro quirk.

Il nostro interprete supporta CHIP-8, CHIP-48, S-CHIP 1.0 e S-CHIP
1.1, in questo modo è in grado di eseguire la stragrande maggioranza
dei videogiochi reperibili in rete.

### Considerazioni finali

Siamo effettivamente riusciti a realizzare un emulatore CHIP-8 in
grado di funzionare su un microcontrollore STM32 come ci eravamo
prefissati.

Alcuni videogiochi purtroppo non hanno un gameplay fluido ma questo è
causato dalla potenza limitata della scheda.

Infine, abbiamo ipotizzato un'ulteriore ottimizzazione permettendo
un'interazione diretta tra l'interprete e il display.

Così però l'interprete perderebbe la sua portabilità.
