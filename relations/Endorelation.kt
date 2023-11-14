//Copyright (c) 2023 Miguel Alejandro Moreno Barrientos
//
//Permission is hereby granted, free of charge, to any person obtaining a copy
//of this software and associated documentation files (the "Software"), to deal
//in the Software without restriction, including without limitation the rights
//to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
//copies of the Software, and to permit persons to whom the Software is
//furnished to do so, subject to the following conditions:
//
//The above copyright notice and this permission notice shall be included in all
//copies or substantial portions of the Software.
//
//THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
//OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
//SOFTWARE.
package relations


/**
 * Analyzer for a finite set and a binary homogenous relation (endorelation) between its elements
 *
 * @param T type of the elements in the set
 * @param set elements in the set
 * @param relation binary homogenous relation between the elements
 * @author Miguel Alejandro Moreno Barrientos, &copy;2023, v0.1.0
 */
class EndoRelation<T>( set: Collection<T>,
                       val relation: EndoRelation<T>.(T, T) -> Boolean )
{
    /**
     * Creates relation from [set] A and a subset of the cartesian product AxA
     *
     * @param set domain set from collection
     * @param pairs set of pairs __{(a,b)&isin;AxA, aRb}__
     */
    constructor( set: Collection<T>,
                 pairs: Set<Pair<T,T>> ) : this( set, { a, b -> a to b in pairs } )

    /**
     * Creates relation from [set] A and a subset of the cartesian product AxA
     *
     * @param set domain set from collection
     * @param pairs pairs __{(a,b)&isin;AxA, aRb}__
     */
    constructor( set: Collection<T>,
                 vararg pairs: Pair<T,T> ) : this( set, pairs.toSet() )

    /**
     * Creates relation from [set] A and adjacency [matrix] as list without checking matrix
     *
     * @param set domain set from collection
     * @param matrix adjacency matrix ({0,1} matrix)
     * @param dummy ambiguity discriminator
     */
    private constructor( set: Collection<T>,
                         matrix: List<List<Int>>,
                         dummy: Unit ) : this( set, { a, b -> matrix[this index a][this index b].toBool } )
    {
        explicitMatrix = matrix
    }

    /**
     * Creates relation from [set] A and adjacency [matrix] as list
     *
     * @param set domain set from collection
     * @param matrix adjacency matrix ({0,1} matrix)
     * @throws IllegalArgumentException [matrix] must be a boolean square matrix with dimension `card(A)`
     */
    constructor( set: Collection<T>,
                 matrix: List<List<Int>> ) : this( set, matrix, Unit )
    {
        if ( matrix.size != set.size || !matrix.all { it.size == set.size } )
            throw IllegalArgumentException( "Malformed matrix" )
        matrix.forEach { row ->
            if ( !row.all { it == 0 || it == 1 } ) throw IllegalArgumentException( "Not {0,1} matrix" )
        }
    }

    /**
     * Creates relation from [set] A and adjacency [matrix] as 2D-Array
     *
     * @param set domain set from collection
     * @param matrix adjacency matrix ({0,1} matrix)
     * @throws IllegalArgumentException [matrix] must be a boolean square matrix with dimension `card(A)`
     */
    constructor( set: Collection<T>,
                 matrix: Array<Array<Int>> ) : this( set, Array(matrix.size) { row -> matrix[row].toList() }.asList() )

    private var explicitMatrix: List<List<Int>>? = null

    /** __Domain set__ of the relation */
    val set: Set<T>

    init
    {
        // Set domain set collection as an immutable set
        this.set = set.toSet()
    }


    /////////////
    // GETTERS
    /////////////

    /** Cardinal of the domain set */
    val cardinal = set.size

    /** Domain set as list */
    val elements by lazy { set.toList() }

    /** Adjacency matrix ({0,1} square matrix) */
    val matrix by lazy {
        explicitMatrix ?: Array(cardinal) { row ->
            IntArray(cardinal) { col -> relation( elements[row], elements[col] ).toInt }.asList()
        }.asList()
    }

    /**
     * Gets adjacency matrix row
     * >&emsp;Sample: __R[[2]][[0]]__ &#8594; `R.matrix[2][0]`
     *
     * @param row row (first element index in the relation)
     * @return integer list with 0s and 1s
     */
    operator fun get( row: Int ) = matrix[row]

    /**
     * Gets adjacency matrix element as boolean in the form ___R[[row],[col]]___
     * >&emsp;Sample: __R[[2,0]]__ &#8594; `R.matrix[2][0].toBool`
     *
     * @param row row (first element index in the relation)
     * @param col column (second element index in the relation)
     * @return ___`aRb`___ as boolean
     */
    operator fun get( row: Int, col: Int ) = matrix[row][col].toBool

    /**
     * Checks if [a] and [b] are related, with [a] as first element in the pair and [b] as the second one
     *
     * @param a first element in the relation
     * @param b second element in the relation
     * @return ___`aRb`___ as boolean
     */
    operator fun invoke( a: T, b: T ) = matrix[ this index a ][ this index b ].toBool

    /**
     * Gets index of an element in the ordered set [elements]
     *
     * @param item element to get index
     * @return index of [item] in the ordered set [elements]
     */
    infix fun index( item: T ) = elements.indexOf(item)

    /**
     * Original set or preimage set (subset with all elements with at least an image)
     * >&emsp;__f^(R)={a, &exist;b, aRb}__
     */
    val preimage by lazy {
        mutableListOf<T>().apply {
            for ( row in matrix.indices )
                if ( !matrix[row].all { it == 0 } )
                    add( elements[row] )
        }.toSet()
    }

    /**
     * Image set (subset with all elements with at least an anti-image)
     * >&emsp;__f(R)={b, &exist;a, aRb}__
     */
    val image by lazy {
        mutableListOf<T>().apply {
            for ( col in matrix.indices )
                if ( !IntArray(cardinal) { row -> matrix[row][col] }.all { it == 0 } )
                    add( elements[col] )
        }.toSet()
    }

    /**
     * Gets elements related to given one which are in the second place of the pair
     * >&emsp;__{b&isin;A, aRb}__
     *
     * @param a prerelated element
     * @see preRelatedTo
     */
    infix fun postRelatedTo( a: T ) = index(a).let { elements.filterIndexed { index, _ -> this[it,index] } }

    /**
     * Gets elements related to given one which are in the first place of the pair
     * >&emsp;__{a&isin;A, aRb}__
     *
     * @param b postrelated element
     * @see postRelatedTo
     */
    infix fun preRelatedTo( b: T ) = index(b).let { elements.filterIndexed { index, _ -> this[index,it] } }


    ////////////////////////////////
    // PROPERTIES OF THE RELATION
    ////////////////////////////////

    /** >&emsp;__{&forall;a, &exist;!b, aRb}__ */
    val isApplication by lazy {
        for ( row in matrix )
            if ( row.count { it > 0 } != 1 )
                return@lazy false

        true
    }

    /**
     * >&emsp;__{&forall;a,b,c, aRc&and;bRc&rarr;a=b}__
     *
     * @see isBijective
     * @see isSurjective
     */
    val isInjective by lazy {
        for ( col in matrix.indices )
            if ( IntArray(matrix.size) { row -> matrix[row][col] }.count( Int::toBool ) > 1 )
                return@lazy false

        true
    }

    /**
     * >&emsp;__{&forall;b, &exist;a, aRb}__
     *
     * @see isBijective
     * @see isInjective
     */
    val isSurjective by lazy {
        for ( col in matrix.indices )
            if ( IntArray(matrix.size) { row -> matrix[row][col] }.all { it == 0 } )
                return@lazy false

        true
    }

    /**
     * >&emsp;__{&forall;b, &exist;!a, aRb}__
     *
     * @see isInjective
     * @see isSurjective
     */
    val isBijective by lazy { isInjective && isSurjective }

    /**
     * >&emsp;__{&forall;a, aRa}__
     *
     * @see isIrreflexive
     */
    val isReflexive by lazy { matrix.withIndex().all { it.value[it.index].toBool } }

    /**
     * >&emsp;__{&forall;a, &not;aRa}__
     *
     * @see isReflexive
     */
    val isIrreflexive by lazy { matrix.withIndex().none { it.value[it.index].toBool } }

    /**
     * >&emsp;__{&forall;a,b, aRb&rarr;bRa}__
     *
     * @see isAntisymmetric
     */
    val isSymmetric by lazy {
        for ( i in matrix.indices )
            for ( j in (i+1) until cardinal )
                if ( this[i,j] != this[j,i] )
                    return@lazy false

        true
    }

    /**
     * >&emsp;__{&forall;a,b, aRb&and;bRa&rarr;a=b}__
     *
     * @see isSymmetric
     */
    val isAntisymmetric by lazy {
        for ( i in matrix.indices )
            for ( j in (i+1) until cardinal )
                if ( this[i,j] && this[j,i] )
                    return@lazy false

        true
    }

    /**
     * Irreflexive and antisymmetric
     * >&emsp;__{&forall;a,b, aRb&rarr;&not;bRa}__
     *
     * @see isAntisymmetric
     * @see isIrreflexive
     */
    val isAsymmetric by lazy { isIrreflexive && isAntisymmetric }

    /**
     * >&emsp;__{&forall;a,b,c, aRb&and;bRc&rarr;aRc}__
     *
     * @see isIntransitive
     * @see isAntitransitive
     * @see isCircular
     */
    val isTransitive by lazy {
        for ( row in matrix.indices )
            for ( col in matrix.indices )
            {
                if ( this[row,col] )
                    continue
                for ( i in matrix.indices )
                    if ( this[row][i] * this[i][col] > 0 )
                        return@lazy false
            }

        true
    }

    /**
     * >&emsp;__{&exist;a,b,c, aRb&and;bRc&and;&not;aRc}__
     *
     * @see isTransitive
     * @see isAntitransitive
     */
    val isIntransitive by lazy { !isTransitive }

    /**
     * >&emsp;__{&forall;a,b,c, aRb&and;bRc&rarr;&not;aRc}__
     *
     * @see isTransitive
     * @see isIntransitive
     */
    val isAntitransitive by lazy {
        for ( row in matrix.indices )
            for ( col in matrix.indices )
            {
                if ( !this[row,col] )
                    continue
                for ( i in matrix.indices )
                    if ( this[row][i] * this[i][col] > 0 )
                        return@lazy false
            }

        true
    }

    /**
     * >&emsp;__{&forall;a,b,c, aRb&and;bRc&rArr;cRa}__
     *
     * @see isTransitive
     */
    val isCircular by lazy {
        for ( row in matrix.indices )
            for ( col in matrix.indices )
            {
                if ( this[col,row] )
                    continue
                for ( i in matrix.indices )
                    if ( this[row][i] * this[i][col] > 0 )
                        return@lazy false
            }

        true
    }

    /**
     * >&emsp;__{&forall;a,b, a&ne;b, aRb&or;bRa}__
     *
     * @see isTotal
     */
    val isConnected by lazy {
        for ( i in matrix.indices )
            for( j in (i+1) until cardinal )
                if ( !(this[i,j] || this[j,i] ) )
                    return@lazy false

        true
    }

    /**
     * Reflexive and connected
     * >&emsp;__{&forall;a,b, aRb&or;bRa}__
     *
     * @see isReflexive
     * @see isConnected
     */
    val isTotal by lazy { isReflexive && isConnected }

    /**
     * Reflexive and symmetric
     *
     * @see isReflexive
     * @see isSymmetric
     */
    val isDependency by lazy { isReflexive && isSymmetric }

    /**
     * Reflexive and transitive
     *
     * @see isReflexive
     * @see isTransitive
     */
    val isPreorder by lazy { isReflexive && isTransitive }

    /** Reflexive, symmetric and transitive (dependency and transitive, or preorder and symmetric)
     *
     * @see isDependency
     * @see isPreorder
     * @see isSymmetric
     * @see isReflexive
     * @see isTransitive
     * @see quotientSet
     */
    val isEquivalence by lazy { isDependency && isTransitive }

    /**
     * Reflexive, antisymmetric and transitive (preorder and antisymmetric)
     *
     * @see isPreorder
     * @see isAntisymmetric
     * @see isReflexive
     * @see isTransitive
     */
    val isPartialOrder by lazy { isPreorder && isAntisymmetric }

    /**
     * Partial order and total
     *
     * @see isPartialOrder
     * @see isTotal
     */
    val isTotalOrder by lazy { isPartialOrder && isTotal }

    /**
     * Irreflexive and transitive (implies asymmetric)
     *
     * @see isIrreflexive
     * @see isTransitive
     */
    val isStrictPartialOrder by lazy { isIrreflexive && isTransitive }

    /**
     * Strict partial order and connected
     *
     * @see isStrictPartialOrder
     * @see isConnected
     */
    val isStrictTotalOrder by lazy { isStrictPartialOrder && isConnected }

    /**
     * Gets __maximal elements__ in the set if it is an order
     *
     * @throws IllegalStateException relation must be an order
     * @see minimals
     * @see maximum
     * @see minimum
     */
    val maximals by lazy {
        if ( !(isPartialOrder || isStrictPartialOrder) )
            throw IllegalStateException("Relation is not an order")

        val value = if ( isPartialOrder ) 1 else 0

        mutableListOf<T>().apply {
            for ( i in matrix.indices )
                if ( matrix[i].count( Int::toBool ) == value )
                    add( elements[i] )
        }
    }

    /**
     * Gets __minimal elements__ in the set if relation is an order
     *
     * @throws IllegalStateException relation must be an order
     * @see maximals
     * @see minimum
     * @see maximum
     */
    val minimals by lazy {
        if ( !(isPartialOrder || isStrictPartialOrder) )
            throw IllegalStateException( "Relation is not an order" )

        val value = if ( isPartialOrder ) 1 else 0

        mutableListOf<T>().apply {
            for ( col in matrix.indices )
                if ( IntArray(matrix.size) { row -> matrix[row][col] }.count( Int::toBool ) == value )
                    add( elements[col] )
        }
    }

    /**
     * Gets __maximum__ in the set if relation is an order or __null__ if it doesn't exist
     *
     * @throws IllegalStateException relation must be an order
     * @see minimum
     * @see maximals
     * @see minimals
     */
    val maximum by lazy {
        if ( !(isPartialOrder || isStrictPartialOrder) )
            throw IllegalStateException("Relation is not an order")

        val value = if ( isPartialOrder ) 1 else 0
        val ssize = cardinal - 1 + value

        for ( i in matrix.indices )
            if ( matrix[i].count( Int::toBool ) == value &&
                IntArray(cardinal) { row -> this[row][i] }.count( Int::toBool ) == ssize )
                return@lazy elements[i]

        null
    }

    /**
     * Gets __minimum__ in the set if it is an order or __null__ if it doesn't exist
     *
     * @throws IllegalStateException relation must be an order
     * @see maximum
     * @see minimals
     * @see maximals
     */
    val minimum by lazy {
        if ( !(isPartialOrder || isStrictPartialOrder) )
            throw IllegalStateException( "Relation is not an order" )

        val value = if ( isPartialOrder ) 1 else 0
        val ssize = cardinal - 1 + value

        for ( i in matrix.indices )
            if ( matrix[i].count( Int::toBool ) == ssize &&
                 IntArray(cardinal) { row -> this[row][i] }.count( Int::toBool ) == value )
                return@lazy elements[i]

        null
    }

    /**
     * Relation has a maximum
     *
     * @see isBoundedBelow
     * @see isBounded
     */
    val isBoundedAbove by lazy { maximum != null }

    /**
     * Relation has a minimum
     *
     * @see isBoundedAbove
     * @see isBounded
     */
    val isBoundedBelow by lazy { minimum != null }

    /**
     * Bounded above and below
     *
     * @see isBoundedAbove
     * @see isBoundedBelow
     */
    val isBounded by lazy { isBoundedAbove && isBoundedBelow }

    // Note: all non-empty finite set with an order is well-founded and well-ordered (if it's total)

    /**
     * Gets quotient set with all equivalence classes as sets
     *
     * @throws IllegalStateException relation must be an equivalence
     * @see isEquivalence
     */
    val quotientSet by lazy {
        if ( !isEquivalence )
            throw IllegalStateException( "Relation is not an equivalence" )

        val qset = mutableSetOf<Set<T>>()
        val notVisited = elements.indices.toMutableList()

        while ( notVisited.isNotEmpty() )
        {
            val elemIdx = notVisited.removeFirst()
            val clazz = mutableSetOf( elements[elemIdx] )
            for ( i in (elemIdx+1) until cardinal )
                if ( this[elemIdx,i] )
                {
                    clazz.add( elements[i] )
                    notVisited.remove( i )
                }
            qset.add( clazz.toSet() )
        }

        qset.toSet()
    }


    //////////////////////////////////
    // OPERATIONS BETWEEN RELATIONS
    //////////////////////////////////

    /**
     * Performs the union between two relation over the same set
     *
     * @param other another relation
     * @throws IllegalArgumentException if domain sets are not the same
     */
    infix fun union( other: EndoRelation<T> ) =
        if ( other.set != set )
            throw IllegalArgumentException( "Domain sets must be the same" )
        else
            EndoRelation(set) l@{ a, b ->
                val idxA = this@EndoRelation index a
                val idxB = this@EndoRelation index b
                this@EndoRelation[idxA,idxB] || other[idxA,idxB]
            }

    /** @see union */
    operator fun plus( other: EndoRelation<T> ) = union( other )

    /**
     * Performs the intersection between two relation over the same set
     *
     * @param other another relation
     * @throws IllegalArgumentException if domain sets are not the same
     */
    infix fun intersection( other: EndoRelation<T> ) =
        if ( other.set != set )
            throw IllegalArgumentException( "Domain sets must be the same" )
        else
            EndoRelation( set ) l@{ a, b ->
                val idxA = this@EndoRelation index a
                val idxB = this@EndoRelation index b
                this@EndoRelation[idxA,idxB] && other[idxA,idxB]
            }

    /** @see intersection */
    operator fun times( other: EndoRelation<T> ) = intersection( other )

    /**
     * Performs the exclusive union between two relation over the same set
     *
     * @param other another relation
     * @throws IllegalArgumentException if domain sets are not the same
     */
    infix fun xor( other: EndoRelation<T> ) =
        if ( other.set != set )
            throw IllegalArgumentException( "Domain sets must be the same" )
        else
            EndoRelation( set ) l@{ a, b ->
                val idxA = this@EndoRelation index a
                val idxB = this@EndoRelation index b
                this@EndoRelation[idxA,idxB] xor other[idxA,idxB]
            }

    /**
     * Performs the composition f(g) over the same set
     *
     * @param other g in f(g)
     * @throws IllegalArgumentException if domain sets are not the same
     */
    infix fun composition( other: EndoRelation<T> ) =
        matrixBooleanProduct( matrix, other.matrix, cardinal ).let {
            if ( set != other.set )
                throw IllegalArgumentException( "Domain sets must be the same" )

            EndoRelation(set) { a, b -> it[this index a][this index b].toBool }
        }

    /** @see composition */
    operator fun invoke( other: EndoRelation<T> ) = composition( other )

    /**
     * Converse _[[transpose, inverse, dual, reciprocal, opposite]]_ relation
     * >&emsp;__Rt={(b,a)&isin;AxA, (a,b)&isin;R}__
     */
    val converseRelation by lazy { EndoRelation( set ) l@{ a, b -> this@EndoRelation( b, a ) } }

    /** @see converseRelation */
    operator fun unaryMinus() = converseRelation

    /** >&emsp;__R'={(a,b)&isin;AxA, (a,b)&notin;R}__ */
    val complementaryRelation by lazy { EndoRelation( set ) l@{ a, b -> !this@EndoRelation( a, b ) } }

    /** @see complementaryRelation */
    operator fun not() = complementaryRelation

    /**
     * Restriction of the relation to the given subset
     * >&emsp;__R/S={(a,b)&isin;SxS&#x2286;AxA, (a,b)&isin;R}__
     *
     * @param subset restriction subset
     * @throws IllegalArgumentException [subset] must be contained in the domain set
     */
    fun restriction( subset: Set<T> ) =
        if ( !set.containsAll( subset ) )
            throw IllegalArgumentException( "Not subset of original set" )
        else
            EndoRelation( subset ) l@{ a, b -> this@EndoRelation(a,b) }

    /** @see restriction */
    operator fun div( subset: Set<T> ) = restriction( subset )

    /**
     * >&emsp;__RC(R)=R&cup;R_identity__
     *
     * @see symmetricClosure
     */
    val reflexiveClosure by lazy {
        EndoRelation( set,
                      Array(cardinal) { row ->
                            IntArray(cardinal) { col ->
                                if ( row != col ) matrix[row][col] else 1 }.asList()
                      }.asList(),
                      Unit )
    }

    /**
     * >&emsp;__RS(R)=R&cup;R_converse__
     *
     * @see reflexiveClosure
     */
    val symmetricClosure by lazy { this + (-this) }


    /////////////////
    // CONVERSIONS
    /////////////////

    /** Endorelation as heterogeneous relation */
    val toRelation by lazy { Relation( set, set, matrix ) }

    /**
     * Relation as a list of pairs of the cartesian product;
     * >&emsp;__[[(a,a),(a,c),(b,a),(b,d),...]]__
     */
    val asPairs by lazy {
        val pairs = mutableListOf<Pair<T,T>>()
        for ( row in matrix.indices )
            for ( col in matrix.indices )
                if ( this[row,col] )
                    pairs.add( Pair( elements[row], elements[col] ) )

        pairs.toList()
    }


    ////////////
    // OTHERS
    ////////////

    /** Compares __set__ and __matrix__ to define relation equality */
    override fun equals(other: Any?): Boolean
    {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as EndoRelation<*>

        if (set != other.set) return false
        if (matrix != other.matrix) return false

        return true
    }

    override fun hashCode(): Int
    {
        var result = set.hashCode()
        result = 31 * result + matrix.hashCode()
        return result
    }

}  // class Endorelation


inline val Boolean.toInt
    get() = if ( this ) 1 else 0

inline val Int.toBool
    get() = this != 0

internal fun matrixBooleanProduct( m1: List<List<Int>>, m2: List<List<Int>>, m2Col: Int ) =
    Array(m1.size) { row ->
        IntArray(m2Col) { col ->
            for ( i in m2.indices )
                if ( m1[row][i] * m2[i][col] > 0 )
                    return@IntArray 1
            0
        }
}
