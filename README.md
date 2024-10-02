# Tries verificados

Como trabajo final de la materia Verificación con F* se realiza la verificación de la estructura de
datos trie.

## Estructura de datos

En este proyecto se verifica la estructura de datos trie. En ella se pueden guardar listas de naturales
que representarían un índice de algún alfabeto. Se representa mediante un árbol cuyos nodos contienen un arreglo de cierta longitud predefinida.

```
noeq
type trie0 (n : U32.t) =
  | L
  | N of raw (trie0 n) n & bool
```

Partimos de una estructura base `trie0` que recibe un parámetro para la longitud del alfabeto a representar. Además contiene un booleano para chequear si el nodo actual es una hoja.

### Invariantes

Para poder probar ciertas propiedades que queremos, necesitamos asegurar algunos invariantes sobre la
estructura.

Se define una función para chequear si se cumplen estos invariantes:

```
let rec is_trie (#alph_size: u32pos) (t: trie0 alph_size) : Tot prop
  =
  match t with
  | L -> true
  | N (a,true) ->
    (forall (i:b_nat alph_size).
      is_trie (index a (U32.uint_to_t i)))
  | N (a,false) ->
    (forall (i:b_nat alph_size).
      is_trie (index a (U32.uint_to_t i)))
    /\
    (exists (i:b_nat alph_size).
        N? (index a (U32.uint_to_t i)))
```

En el caso de un nodo hay que chequear que todos los elementos del arreglo sean tries para los cuales
valen los invariantes. Si el nodo no es una hoja debe haber al menos algún elemento del arreglo que
sea otro nodo (o sea no puede haber un nodo que no sea hoja y todos sus hijos sean L).

### Implementacion

Algunas consideraciones sobre la implementación:
- Los elementos de las listas que se guardan son `b_nat`s. Es decir naturales 'boundeados' para
que se puedan transformar en unsigned de 32 bits.
- Se incluye el lema `index_dec` que se asume como válido, para poder probar lemas que hagan recursión
sobre la estructura, accediendo a los arreglos.

## Propiedades

Planteado todo esto, se realizan las pruebas correspondientes:

### Operadores preservan invariante

Primero hay que probar que los operadores `insert0` y `delete0` preservan los invariantes.
Es decir, por ejemplo:

```
Lemma (requires is_trie t) (ensures is_trie (insert0 l t))
```

### Trie como conjunto

Finalmente se realizan las pruebas para asegurar que los tries definidos junto a sus operaciones
modelan conjuntos de listas de `b_nat`s. Para ello se instancia la clase `container` con `trie`s, junto
a sus lemas correspondientes.
