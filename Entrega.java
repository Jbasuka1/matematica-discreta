import java.lang.AssertionError;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.function.BiPredicate;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Stream;

/*
 * Aquesta entrega consisteix en implementar tots els mètodes annotats amb "// TODO". L'enunciat de
 * cada un d'ells és al comentari de la seva signatura i exemples del seu funcionament als mètodes
 * `Tema1.tests`, `Tema2.tests`, etc.
 *
 * L'avaluació consistirà en:
 *
 * - Si el codi no compila, la nota del grup serà un 0.
 *
 * - Si heu fet cap modificació que no sigui afegir un mètode, afegir proves als mètodes "tests()" o
 *   implementar els mètodes annotats amb "// TODO", la nota del grup serà un 0.
 *
 * - Principalment, la nota dependrà del correcte funcionament dels mètodes implemnetats (provant
 *   amb diferents entrades).
 *
 * - Tendrem en compte la neteja i organització del codi. Un estandard que podeu seguir és la guia
 *   d'estil de Google per Java: https://google.github.io/styleguide/javaguide.html . Algunes
 *   consideracions importants:
 *    + Entregau amb la mateixa codificació (UTF-8) i finals de línia (LF, no CR+LF)
 *    + Indentació i espaiat consistent
 *    + Bona nomenclatura de variables
 *    + Declarar les variables el més aprop possible al primer ús (és a dir, evitau blocs de
 *      declaracions).
 *    + Convé utilitzar el for-each (for (int x : ...)) enlloc del clàssic (for (int i = 0; ...))
 *      sempre que no necessiteu l'índex del recorregut.
 *
 * Per com està plantejada aquesta entrega, no necessitau (ni podeu) utilitzar cap `import`
 * addicional, ni qualificar classes que no estiguin ja importades. El que sí podeu fer és definir
 * tots els mètodes addicionals que volgueu (de manera ordenada i dins el tema que pertoqui).
 *
 * Podeu fer aquesta entrega en grups de com a màxim 3 persones, i necessitareu com a minim Java 10.
 * Per entregar, posau a continuació els vostres noms i entregau únicament aquest fitxer.
 * - Nom 1: Carlos Alejandro Pizzi Salas
 * - Nom 2: Bratlie Joao Bastidas Rivera
 * - Nom 3:
 *
 * L'entrega es farà a través d'una tasca a l'Aula Digital que obrirem abans de la data que se us
 * hagui comunicat i vos recomanam que treballeu amb un fork d'aquest repositori per seguir més
 * fàcilment les actualitzacions amb enunciats nous. Si no podeu visualitzar bé algun enunciat,
 * assegurau-vos de que el vostre editor de texte estigui configurat amb codificació UTF-8.
 */
class Entrega {
  /*
   * Aquí teniu els exercicis del Tema 1 (Lògica).
   *
   * La majoria dels mètodes reben de paràmetre l'univers (representat com un array) i els predicats
   * adients (per exemple, `Predicate<Integer> p`). Per avaluar aquest predicat, si `x` és un
   * element de l'univers, podeu fer-ho com `p.test(x)`, que té com resultat un booleà (true si
   * `P(x)` és cert). Els predicats de dues variables són de tipus `BiPredicate<Integer, Integer>` i
   * similarment s'avaluen com `p.test(x, y)`.
   *
   * En cada un d'aquests exercicis (excepte el primer) us demanam que donat l'univers i els
   * predicats retorneu `true` o `false` segons si la proposició donada és certa (suposau que
   * l'univers és suficientment petit com per poder provar tots els casos que faci falta).
   */
  static class Tema1 {
    /*
     * Donat n > 1, en quants de casos (segons els valors de veritat de les proposicions p1,...,pn)
     * la proposició (...((p1 -> p2) -> p3) -> ...) -> pn és certa?
     *
     * Vegeu el mètode Tema1.tests() per exemples.
     */
    static int exercici1(int n) {
      int contador = 0;
      int numeroCombinaciones = (int) Math.pow(2, n);
      for (int caso = 0; caso < numeroCombinaciones; caso++){
        boolean resultado = true;
        for(int j = 0; j < n; j++){
          boolean verdadero = ((caso & (1 << j)) != 0);
          resultado = (!resultado || verdadero);
        }
        if (resultado) {
          contador++;
        }
      } 
      return contador;
    }

    /*
     * És cert que ∀x : P(x) -> ∃!y : Q(x,y) ?
     */
    static boolean exercici2(int[] universe, Predicate<Integer> p, BiPredicate<Integer, Integer> q) {
      for (int x : universe) {
        if (p.test(x)) {
          boolean unicaY = false;
          for (int y : universe) {
            if (q.test(x, y)) {
              if (!unicaY) {
                unicaY = true;
              } else {
                return false;
              }
            }
          }
          if (!unicaY) {
            return false;
          }
        }
      }
      return true;
    }

    /*
     * És cert que ∃x : ∀y : Q(x, y) -> P(x) ?
     */
    static boolean exercici3(int[] universe, Predicate<Integer> p, BiPredicate<Integer, Integer> q) {
      for (int x : universe) {
        boolean paraTodoY = true;
        for (int y : universe) {
          if (q.test(x, y)) {
            if (!p.test(x)) {
              paraTodoY = false;
              break;
            }
          }
        }
        if (paraTodoY) {
          return true;
        }
      }
      return false;
    }

    /*
     * És cert que ∃x : ∃!y : ∀z : P(x,z) <-> Q(y,z) ?
     */
    static boolean exercici4(int[] universe, BiPredicate<Integer, Integer> p, BiPredicate<Integer, Integer> q) {
      for (int x : universe) {
        boolean unicaY = false;
        for (int y : universe) {
          boolean paraTodoZ = true;
          for (int z : universe) {
            if (!(p.test(x, z) == q.test(y, z))) {
              paraTodoZ = false;
              break;
            }
          }
          if (paraTodoZ) {
            if (unicaY) {
              unicaY = false;
              break;
            } else {
              unicaY = true;
            }
          }
        }
        if (unicaY) {
          return true;
        }
      }
      return false;
    }

    /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
     */
    static void tests() {
      // Exercici 1

      // p1 -> p2 és cert exactament a 3 files
      // p1 p2
      // 0  0  <-
      // 0  1  <-
      // 1  0
      // 1  1  <-
      assertThat(exercici1(2) == 3);

      // (p1 -> p2) -> p3 és cert exactament a 5 files
      // p1 p2 p3
      // 0  0  0
      // 0  0  1  <-
      // 0  1  0
      // 0  1  1  <-
      // 1  0  0  <-
      // 1  0  1  <-
      // 1  1  0
      // 1  1  1  <-
      assertThat(exercici1(3) == 5);

      // Exercici 2
      // ∀x : P(x) -> ∃!y : Q(x,y)
      assertThat(
          exercici2(
            new int[] { 1, 2, 3 },
            x -> x % 2 == 0,
            (x, y) -> x+y >= 5
          )
      );

      assertThat(
          !exercici2(
            new int[] { 1, 2, 3 },
            x -> x < 3,
            (x, y) -> x-y > 0
          )
      );

      // Exercici 3
      // És cert que ∃x : ∀y : Q(x, y) -> P(x) ?
      assertThat(
          exercici3(
            new int[] { 1, 2, 3, 4, 5, 6, 7, 8, 9 },
            x -> x % 3 != 0,
            (x, y) -> y % x == 0
          )
      );

      assertThat(
          exercici3(
            new int[] { 1, 2, 3, 4, 5, 6, 7, 8, 9 },
            x -> x % 4 != 0,
            (x, y) -> (x*y) % 4 != 0
          )
      );

      // Exercici 4
      // És cert que ∃x : ∃!y : ∀z : P(x,z) <-> Q(y,z) ?
      assertThat(
          exercici4(
            new int[] { 0, 1, 2, 3, 4, 5 },
            (x, z) -> x*z == 1,
            (y, z) -> y*z == 2
          )
      );

      assertThat(
          !exercici4(
            new int[] { 2, 3, 4, 5 },
            (x, z) -> x*z == 1,
            (y, z) -> y*z == 2
          )
      );
    }
  }

  /*
   * Aquí teniu els exercicis del Tema 2 (Conjunts).
   *
   * Per senzillesa tractarem els conjunts com arrays (sense elements repetits). Per tant, un
   * conjunt de conjunts d'enters tendrà tipus int[][].
   *
   * Les relacions també les representarem com arrays de dues dimensions, on la segona dimensió
   * només té dos elements. Per exemple
   *   int[][] rel = {{0,0}, {0,1}, {1,1}, {2,2}};
   * i també donarem el conjunt on està definida, per exemple
   *   int[] a = {0,1,2};
   * Als tests utilitzarem extensivament la funció generateRel definida al final (també la podeu
   * utilitzar si la necessitau).
   *
   * Les funcions f : A -> B (on A i B son subconjunts dels enters) les representam o bé amb el seu
   * graf o amb un objecte de tipus Function<Integer, Integer>. Sempre donarem el domini int[] a, el
   * codomini int[] b. En el cas de tenir un objecte de tipus Function<Integer, Integer>, per aplicar
   * f a x, és a dir, "f(x)" on x és d'A i el resultat f.apply(x) és de B, s'escriu f.apply(x).
   */
  static class Tema2 {
    /*
     * Calculau el nombre d'elements del conjunt (a u b) × (a \ c)
     *
     * Podeu soposar que `a`, `b` i `c` estan ordenats de menor a major.
     */
    static int exercici1(int[] a, int[] b, int[] c) {
      HashSet<Integer> unionAB = new HashSet<>();
      for (int elemento : a) {
        unionAB.add(elemento);
      }
      for (int elemento : b) {
        unionAB.add(elemento);
      }
      
      HashSet<Integer> diferenciaAC = new HashSet<>();
      HashSet<Integer> C = new HashSet<>();
      for (int elemento : c) {
        C.add(elemento);
      }
      for (int elemento : a) {
        if (!C.contains(elemento)) {
          diferenciaAC.add(elemento);
        }
      }
      return unionAB.size() * diferenciaAC.size();
    }

    /*
     * La clausura d'equivalència d'una relació és el resultat de fer-hi la clausura reflexiva, simètrica i
     * transitiva simultàniament, i, per tant, sempre és una relació d'equivalència.
     *
     * Trobau el cardinal d'aquesta clausura.
     *
     * Podeu soposar que `a` i `rel` estan ordenats de menor a major (`rel` lexicogràficament).
     */
    static int exercici2(int[] a, int[][] rel) {
      List<int[]> listaRelacion = new ArrayList<>(Arrays.asList(rel));
      // Clausura reflexiva
      for (int elemento : a) {
        boolean encontrado = false;
        for (int[] par : listaRelacion) {
          if (par[0] == elemento && par[1] == elemento) {
            encontrado = true;
            break;
          }
        }
        if (!encontrado) {
          listaRelacion.add(new int[]{elemento, elemento});
        }
      }
      // Clausura simétrica
      List<int[]> clausuraSimetrica = new ArrayList<>(listaRelacion);
      for (int[] par : listaRelacion) {
        boolean encontrado = false;
        for (int[] parSimetrico : clausuraSimetrica) {
          if (parSimetrico[0] == par[1] && parSimetrico[1] == par[0]) {
            encontrado = true;
            break;
          }
        }
        if (!encontrado) {
          clausuraSimetrica.add(new int[]{par[1], par[0]});
        }
      }
      listaRelacion = clausuraSimetrica;
      // Clausura transitiva
      boolean added = true;
      while (added) {
        added = false;
        List<int[]> paresNuevos = new ArrayList<>(listaRelacion);
        for (int[] par1 : listaRelacion) {
          for (int[] par2 : listaRelacion) {
            if (par1[1] == par2[0]) {
              boolean encontrado = false;
              for (int[] parTransicion : paresNuevos) {
                if (parTransicion[0] == par1[0] && parTransicion[1] == par2[1]) {
                  encontrado = true;
                  break;
                }
              }
              if (!encontrado) {
                paresNuevos.add(new int[]{par1[0], par2[1]});
                added = true;
              }
            }
          }
        }
        listaRelacion = paresNuevos;
      }
      return listaRelacion.size();
    } 
    

    /*
     * Comprovau si la relació `rel` és un ordre total sobre `a`. Si ho és retornau el nombre
     * d'arestes del seu diagrama de Hasse. Sino, retornau -2.
     *
     * Podeu soposar que `a` i `rel` estan ordenats de menor a major (`rel` lexicogràficament).
     */
    static int exercici3(int[] a, int[][] rel) {
      int n = a.length;
      boolean[][] relacion = new boolean[n][n];
      // Llenar la matriz de relación
      for (int[] par : rel) {
        int i = indiceDe(a, par[0]);
        int j = indiceDe(a, par[1]);
        relacion[i][j] = true;
      }
      // Comprobar reflexividad
      for (int i = 0; i < n; i++) {
        if (!relacion[i][i]) {
          return -2;
        }
      }
      // Comprobar antisimetría
      for (int i = 0; i < n; i++) {
        for (int j = 0; j < n; j++) {
          if (i != j && relacion[i][j] && relacion[j][i]) {
            return -2;
          }
        }
      }
      // Comprobar transitividad
      for (int i = 0; i < n; i++) {
        for (int j = 0; j < n; j++) {
          for (int k = 0; k < n; k++) {
            if (relacion[i][j] && relacion[j][k] && !relacion[i][k]) {
              return -2;
            }
          }
        }
      }
      // Comprobar totalidad
      for (int i = 0; i < n; i++) {
        for (int j = i + 1; j < n; j++) {
          if (!relacion[i][j] && !relacion[j][i]) {
            return -2;
          }
        }
      }
      boolean[][] Hasse = new boolean[n][n];
      for (int i = 0; i < n; i++) {
        for (int j = 0; j < n; j++) {
          if (i != j && relacion[i][j]) {
            boolean esAristaHasse = true;
            for (int k = 0; k < n; k++) {
              if (k != i && k != j && relacion[i][k] && relacion[k][j]) {
                esAristaHasse = false;
                break;
              }
            }
            if (esAristaHasse) {
              Hasse[i][j] = true;
            }
          }
        }
      }
      // Contar el número de aristas en el diagrama de Hasse
      int contadorAristas = 0;
      for (boolean[] fila : Hasse) {
        for (boolean esArista : fila) {
          if (esArista) {
            contadorAristas++;
          }
        }
      }
      return contadorAristas;
    }
    
    static int indiceDe(int[] conjunto, int elemento) {
      int indice = 0;
      for (int elementoA : conjunto) {
        if (elementoA == elemento) {
          return indice;
        }
        indice++;
      }
      return -1;
    }
    
    /*
     * Comprovau si les relacions `rel1` i `rel2` són els grafs de funcions amb domini i codomini
     * `a`. Si ho son, retornau el graf de la composició `rel2 ∘ rel1`. Sino, retornau null.
     *
     * Podeu soposar que `a`, `rel1` i `rel2` estan ordenats de menor a major (les relacions,
     * lexicogràficament).
     */
    static int[][] exercici4(int[] a, int[][] rel1, int[][] rel2) {
      if (!esFuncio(a, rel1) || !esFuncio(a, rel2)) {
        return null; 
      }
      return composicion(rel1, rel2);
    }
    
    static boolean esFuncio(int[] a, int[][] rel) {
      for (int i = 0; i < a.length; i++) {
        int x = a[i];
        boolean encontrado = false;
        for (int j = 0; j < rel.length; j++) {
          if (rel[j][0] == x) {
            if (encontrado) {
              return false;
            }
            encontrado = true;
          }
        }
        if (!encontrado) {
          return false;
        }
      }
      return true;
    }
    
    static int[][] composicion(int[][] rel1, int[][] rel2) {
      List<int[]> composicion = new ArrayList<>();
      for (int[] par1 : rel1) {
        for (int[] par2 : rel2) {
          if (par1[1] == par2[0]) {
            composicion.add(new int[]{par1[0], par2[1]});
          }
        }
      }
      return composicion.toArray(new int[0][0]);
    }
    
    /*
     * Comprovau si la funció `f` amb domini `dom` i codomini `codom` té inversa. Si la té, retornau
     * el seu graf (el de l'inversa). Sino, retornau null.
     */
    static int[][] exercici5(int[] dom, int[] codom, Function<Integer, Integer> f) {
      boolean[] visitado = new boolean[codom.length];
      List<int[]> g = new ArrayList<>();
      for (int y : codom) {
        boolean antiImagenEncontrado = false;
        for (int j = 0; j < dom.length; j++) {
          int x = dom[j];
          if (f.apply(x) == y && !visitado[j]) {
            g.add(new int[]{y, x});
            visitado[j] = true;
            antiImagenEncontrado = true;
            break;
          }
        }
        if (!antiImagenEncontrado) {
          return null;
        }
      }
        
      int[][] resultado = new int[g.size()][2];
      for (int i = 0; i < g.size(); i++) {
        resultado[i] = g.get(i);
      }
      return resultado;
    }

    /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
     */
    static void tests() {
      // Exercici 1
      // |(a u b) × (a \ c)|

      assertThat(
          exercici1(
            new int[] { 0, 1, 2 },
            new int[] { 1, 2, 3 },
            new int[] { 0, 3 }
          )
          == 8
      );

      assertThat(
          exercici1(
            new int[] { 0, 1 },
            new int[] { 0 },
            new int[] { 0 }
          )
          == 2
      );

      // Exercici 2
      // nombre d'elements de la clausura d'equivalència

      final int[] int08 = { 0, 1, 2, 3, 4, 5, 6, 7, 8 };

      assertThat(exercici2(int08, generateRel(int08, (x, y) -> y == x + 1)) == 81);

      final int[] int123 = { 1, 2, 3 };

      assertThat(exercici2(int123, new int[][] { {1, 3} }) == 5);

      // Exercici 3
      // Si rel és un ordre total, retornar les arestes del diagrama de Hasse

      final int[] int05 = { 0, 1, 2, 3, 4, 5 };

      assertThat(exercici3(int05, generateRel(int05, (x, y) -> x >= y)) == 5);
      assertThat(exercici3(int08, generateRel(int05, (x, y) -> x <= y)) == -2);

      // Exercici 4
      // Composició de grafs de funcions (null si no ho son)

      assertThat(
          exercici4(
            int05,
            generateRel(int05, (x, y) -> x*x == y),
            generateRel(int05, (x, y) -> x == y)
          )
          == null
      );


      var ex4test2 = exercici4(
          int05,
          generateRel(int05, (x, y) -> x + y == 5),
          generateRel(int05, (x, y) -> y == (x + 1) % 6)
        );

      assertThat(
          Arrays.deepEquals(
            lexSorted(ex4test2),
            generateRel(int05, (x, y) -> y == (5 - x + 1) % 6)
          )
      );

      // Exercici 5
      // trobar l'inversa (null si no existeix)

      assertThat(exercici5(int05, int08, x -> x + 3) == null);

      assertThat(
          Arrays.deepEquals(
            lexSorted(exercici5(int08, int08, x -> 8 - x)),
            generateRel(int08, (x, y) -> y == 8 - x)
          )
      );
    }

    /**
     * Ordena lexicogràficament un array de 2 dimensions
     * Per exemple:
     *  arr = {{1,0}, {2,2}, {0,1}}
     *  resultat = {{0,1}, {1,0}, {2,2}}
     */
    static int[][] lexSorted(int[][] arr) {
      if (arr == null)
        return null;

      var arr2 = Arrays.copyOf(arr, arr.length);
      Arrays.sort(arr2, Arrays::compare);
      return arr2;
    }

    /**
     * Genera un array int[][] amb els elements {a, b} (a de as, b de bs) que satisfàn pred.test(a, b)
     * Per exemple:
     *   as = {0, 1}
     *   bs = {0, 1, 2}
     *   pred = (a, b) -> a == b
     *   resultat = {{0,0}, {1,1}}
     */
    static int[][] generateRel(int[] as, int[] bs, BiPredicate<Integer, Integer> pred) {
      var rel = new ArrayList<int[]>();

      for (int a : as) {
        for (int b : bs) {
          if (pred.test(a, b)) {
            rel.add(new int[] { a, b });
          }
        }
      }

      return rel.toArray(new int[][] {});
    }

    /// Especialització de generateRel per a = b
    static int[][] generateRel(int[] as, BiPredicate<Integer, Integer> pred) {
      return generateRel(as, as, pred);
    }
  }
  
  /*
   * Aquí teniu els exercicis del Tema 3 (Grafs).
   *
   * Els (di)grafs vendran donats com llistes d'adjacència (és a dir, tractau-los com diccionaris
   * d'adjacència on l'índex és la clau i els vèrtexos estan numerats de 0 a n-1). Per exemple,
   * podem donar el graf cicle d'ordre 3 com:
   *
   * int[][] c3dict = {
   *   {1, 2}, // veïns de 0
   *   {0, 2}, // veïns de 1
   *   {0, 1}  // veïns de 2
   * };
   *
   * **NOTA: Els exercicis d'aquest tema conten doble**
   */
  static class Tema3 {
    /*
     * Determinau si el graf és connex. Podeu suposar que `g` no és dirigit.
     */
    static boolean exercici1(int[][] g) {
      int n = g.length;
      if (n <= 1) {
        return true;
      }      
      boolean[] visitado = new boolean[n];
      nodosConexos(g, 0, visitado);
      for (int i = 0; i < n; i++) {
        if (!visitado[i]) {
          return false;
        }
      }
      return true;
    }

    /*
     * Donat un tauler d'escacs d'amplada `w` i alçada `h`, determinau quin és el mínim nombre de
     * moviments necessaris per moure un cavall de la casella `i` a la casella `j`.
     *
     * Les caselles estan numerades de `0` a `w*h-1` per files. Per exemple, si w=5 i h=2, el tauler
     * és:
     *   0 1 2 3 4
     *   5 6 7 8 9
     *
     * Retornau el nombre mínim de moviments, o -1 si no és possible arribar-hi.
     */
    static int exercici2(int w, int h, int i, int j) {
      if (i < 0 || i >= w * h || j < 0 || j >= w * h) {
        return -1;
      }
      List<int[]> cola = new ArrayList<>();
      int inicioX = i % w;
      int inicioY = i / w;
      cola.add(new int[]{inicioY, inicioX});
      
      boolean[][] visitado = new boolean[h][w];
      visitado[inicioY][inicioX] = true;
      
      int[][] distancia = new int[h][w];
      distancia[inicioY][inicioX] = 0;
      
      int finX = j % w;
      int finY = j / w;
      int[][] movimientosCaballo = {
        {-2, -1}, {-1, -2}, {1, -2}, {2, -1},
        {2, 1}, {1, 2}, {-1, 2}, {-2, 1}
      };
      while (!cola.isEmpty()) {
        int[] actual = cola.remove(0);
        int x = actual[1];
        int y = actual[0];
        if (x == finX && y == finY) {
          return distancia[y][x];
        }
        for (int[] movimiento : movimientosCaballo) {
          int nuevaX = x + movimiento[1];
          int nuevaY = y + movimiento[0];
          if (nuevaX >= 0 && nuevaX < w && nuevaY >= 0 && nuevaY < h && !visitado[nuevaY][nuevaX]) {
            visitado[nuevaY][nuevaX] = true;
            distancia[nuevaY][nuevaX] = distancia[y][x] + 1;
            cola.add(new int[]{nuevaY, nuevaX});
          }
        }
      }
      return -1;
    }

    /*
     * Donat un arbre arrelat (graf dirigit `g`, amb arrel `r`), decidiu si el vèrtex `u` apareix
     * abans (o igual) que el vèrtex `v` al recorregut en preordre de l'arbre.
     */
    static boolean exercici3(int[][] g, int r, int u, int v) {
      int n = g.length; 
      int[] preorden = new int[n];
      Arrays.fill(preorden, -1);
      int[] indice = {0}; 
      
      preordenar(g, r, preorden, indice);

      int preordenU = preorden[u];
      int preordenV = preorden[v];
      return preordenU <= preordenV;
    }

    /*
     * Donat un recorregut en preordre (per exemple, el primer vèrtex que hi apareix és `preord[0]`)
     * i el grau de cada vèrtex (per exemple, el vèrtex `i` té grau `d[i]`), trobau l'altura de
     * l'arbre corresponent.
     *
     * L'altura d'un arbre arrelat és la major distància de l'arrel a les fulles.
     */
    static int exercici4(int[] preord, int[] d) {
      return -1; // TO DO
    }

    static void nodosConexos(int[][] g, int nodo, boolean[] visitado) {
      visitado[nodo] = true;
      for (int vecino : g[nodo]) {
        if (!visitado[vecino]) {
          nodosConexos(g, vecino, visitado);
        }
      }
    }
    
    static void preordenar(int[][] g, int nodo, int[] preorden, int[] indice) {
        preorden[nodo] = indice[0];
        indice[0]++;

        for (int vecino : g[nodo]) {
            if (preorden[vecino] == -1) {
                preordenar(g, vecino, preorden, indice);
            }
        }
    }
    /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
     */
    static void tests() {
      // Exercici 1
      // G connex?

      final int[][] B2 = { {}, {} };

      final int[][] C3 = { {1, 2}, {0, 2}, {0, 1} };

      final int[][] C3D = { {1}, {2}, {0} };

      assertThat(exercici1(C3));
      assertThat(!exercici1(B2));

      // Exercici 2
      // Moviments de cavall

      // Tauler 4x3. Moviments de 0 a 11: 3.
      // 0  1   2   3
      // 4  5   6   7
      // 8  9  10  11
      assertThat(exercici2(4, 3, 0, 11) == 3);

      // Tauler 3x2. Moviments de 0 a 2: (impossible).
      // 0 1 2
      // 3 4 5
      assertThat(exercici2(3, 2, 0, 2) == -1);

      // Exercici 3
      // u apareix abans que v al recorregut en preordre (o u=v)

      final int[][] T1 = {
        {1, 2, 3, 4},
        {5},
        {6, 7, 8},
        {},
        {9},
        {},
        {},
        {},
        {},
        {10, 11},
        {},
        {}
      };

      assertThat(exercici3(T1, 0, 5, 3));
      assertThat(!exercici3(T1, 0, 6, 2));

      // Exercici 4
      // Altura de l'arbre donat el recorregut en preordre

      final int[] P1 = { 0, 1, 5, 2, 6, 7, 8, 3, 4, 9, 10, 11 };
      final int[] D1 = { 4, 1, 3, 0, 1, 0, 0, 0, 0, 2,  0,  0 };

      final int[] P2 = { 0, 1, 2, 3, 4, 5, 6, 7, 8 };
      final int[] D2 = { 2, 0, 2, 0, 2, 0, 2, 0, 0 };

      assertThat(exercici4(P1, D1) == 3);
      assertThat(exercici4(P2, D2) == 4);
    }
  }

  /*
   * Aquí teniu els exercicis del Tema 4 (Aritmètica).
   *
   * En aquest tema no podeu:
   *  - Utilitzar la força bruta per resoldre equacions: és a dir, provar tots els nombres de 0 a n
   *    fins trobar el que funcioni.
   *  - Utilitzar long, float ni double.
   *
   * Si implementau algun dels exercicis així, tendreu un 0 d'aquell exercici.
   */
  static class Tema4 {
    /*
     * Calculau el mínim comú múltiple de `a` i `b`.
     */
    static int exercici1(int a, int b) {
      if (a == 0 || b == 0) {
        return 0;
      }
      int A = Math.abs(a);
      int B = Math.abs(b);
      int mcd = euclidMCD(A, B);
      int mcm = A / mcd * B;
      return mcm;
    }

    /*
     * Trobau totes les solucions de l'equació
     *
     *   a·x ≡ b (mod n)
     *
     * donant els seus representants entre 0 i n-1.
     *
     * Podeu suposar que `n > 1`. Recordau que no no podeu utilitzar la força bruta.
     */
    static int[] exercici2(int a, int b, int n) {
      if (a == 0) {
            if (b % n == 0) {
                return new int[]{0};
            } else {
                return new int[]{};
            }
        }
        b = (b % n + n) % n;
        int mcd = euclidMCD(a, n);
        if (b % mcd != 0) {
            return new int[]{};
        }
        int[] solucionParticular = euclidExtendido(a, n);
        int x0 = solucionParticular[0] * (b / mcd) % n;
        List<Integer> soluciones = new ArrayList<>();
        for (int k = 0; k < mcd; k++) {
            int x = (x0 + k * (n / mcd)) % n;
            if (x < 0) {
                x += n;
            }
            soluciones.add(x);
        }

        int[] resultado = new int[soluciones.size()];
        for (int i = 0; i < soluciones.size(); i++) {
            resultado[i] = soluciones.get(i);
        }
        return resultado;
    }

    /*
     * Donats `a != 0`, `b != 0`, `c`, `d`, `m > 1`, `n > 1`, determinau si el sistema
     *
     *   a·x ≡ c (mod m)
     *   b·x ≡ d (mod n)
     *
     * té solució.
     */
    static boolean exercici3(int a, int b, int c, int d, int m, int n) {
      return false; // TO DO
    }

    /*
     * Donats `n` un enter, `k > 0` enter, i `p` un nombre primer, retornau el residu de dividir n^k
     * entre p.
     *
     * Alerta perquè és possible que n^k sigui massa gran com per calcular-lo directament.
     * De fet, assegurau-vos de no utilitzar cap valor superior a max{n, p²}.
     *
     * Anau alerta també abusant de la força bruta, la vostra implementació hauria d'executar-se en
     * qüestió de segons independentment de l'entrada.
     */
    static int exercici4(int n, int k, int p) {
      return -1; // TO DO
    }
    
    static int euclidMCD(int a, int b) {
      while (b != 0) {
        int temp = b;
        b = a % b;
        a = temp;
      }
      return a;
    }
    
    static int[] euclidExtendido(int a, int b) {
      int x0 = 1, y0 = 0, x1 = 0, y1 = 1;
      while (b != 0) {
        int q = a / b;
        int temp = b;
        b = a % b;
        a = temp;
        temp = x1;
        x1 = x0 - q * x1;
        x0 = temp;
        temp = y1;
        y1 = y0 - q * y1;
        y0 = temp;
      }
      return new int[]{x0, y0};
    }

    /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
     */
    static void tests() {
      // Exercici 1
      // mcm(a, b)

      assertThat(exercici1(35, 77) == 5*7*11);
      assertThat(exercici1(-8, 12) == 24);

      // Exercici 2
      // Solucions de a·x ≡ b (mod n)

      assertThat(Arrays.equals(exercici2(2, 2, 4), new int[] { 1, 3 }));
      assertThat(Arrays.equals(exercici2(3, 2, 4), new int[] { 2 }));

      // Exercici 3
      // El sistema a·x ≡ c (mod m), b·x ≡ d (mod n) té solució?

      assertThat(exercici3(3, 2, 2, 2, 5, 4));
      assertThat(!exercici3(3, 2, 2, 2, 10, 4));

      // Exercici 4
      // n^k mod p

      assertThat(exercici4(2018, 2018, 5) == 4);
      assertThat(exercici4(-2147483646, 2147483645, 46337) == 7435);
    }
  }

  /**
   * Aquest mètode `main` conté alguns exemples de paràmetres i dels resultats que haurien de donar
   * els exercicis. Podeu utilitzar-los de guia i també en podeu afegir d'altres (no els tendrem en
   * compte, però és molt recomanable).
   *
   * Podeu aprofitar el mètode `assertThat` per comprovar fàcilment que un valor sigui `true`.
   */
  public static void main(String[] args) {
    Tema1.tests();
    Tema2.tests();
    Tema3.tests();
    Tema4.tests();
  }

  /// Si b és cert, no fa res. Si b és fals, llança una excepció (AssertionError).
  static void assertThat(boolean b) {
    if (!b)
      throw new AssertionError();
  }
}

// vim: set textwidth=100 shiftwidth=2 expandtab :
