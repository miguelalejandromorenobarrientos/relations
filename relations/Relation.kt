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
 * Analyzer for two finite sets and a binary heterogeneous relation between its elements
 *
 * @param T type of the elements in the domain set
 * @param S type of the elements in the codomain set
 * @param domainSet elements in the domain set
 * @param codomainSet elements in the codomain set
 * @param relation binary heterogeneous relation between the elements
 * @author Miguel Alejandro Moreno Barrientos, &copy;2023, v0.1.0
 */
class Relation<T,S>( domainSet: Collection<T>,
                     codomainSet: Collection<S>,
                     val relation: Relation<T,S>.(T, S) -> Boolean )
{
    /**
     * Creates relation from domain A and codomain B and a subset of AxB
     *
     * @param domainSet domain set from collection
     * @param codomainSet codomain set from collection
     * @param pairs pairs set __{(a,b)&isin;aRb&sub;AxB}__
     */
    constructor( domainSet: Collection<T>,
                 codomainSet: Collection<S>,
                 pairs: Set<Pair<T,S>> ) : this( domainSet, codomainSet, { a, b -> a to b in pairs } )

    /**
     * Creates relation from domain and codomain and a subset of AxB
     *
     * @param domainSet domain set from collection
     * @param codomainSet codomain set from collection
     * @param pairs pairs __{(a,b)&isin;aRb&sub;AxB}__
     */
    constructor( domainSet: Collection<T>,
                 codomainSet: Collection<S>,
                 vararg pairs: Pair<T,S> ) : this( domainSet, codomainSet, pairs.toSet() )

    /**
     * Creates relation from domain A, codomain B and adjacency [matrix]
     *
     * @param domainSet domain set from collection
     * @param codomainSet codomain set from collection
     * @param matrix adjacency matrix ({0,1} matrix)
     * @throws IllegalArgumentException [matrix] must be a boolean matrix with dimension `card(A)xCard(B)`
     */
    constructor( domainSet: Collection<T>,
                 codomainSet: Collection<S>,
                 matrix: List<List<Int>> )
    : this( domainSet, codomainSet, { a, b -> matrix[this domainIndex a][this codomainIndex b].toBool } )
    {
        if ( matrix.size != domainCardinal || !matrix.all { it.size == codomainCardinal } )
            throw IllegalArgumentException( "Malformed matrix" )
        matrix.forEach { row ->
            if ( !row.all { it == 0 || it == 1 } ) throw IllegalArgumentException( "Not {0,1} matrix" )
        }

        explicitMatrix = matrix
    }

    /**
     * Creates relation from domain A, codomain B and adjacency [matrix] as 2D-Array
     *
     * @param domainSet domain set from collection
     * @param codomainSet codomain set from collection
     * @param matrix adjacency matrix ({0,1} matrix)
     * @throws IllegalArgumentException [matrix] must be a boolean matrix with dimension `card(A)xCard(B)`
     */
    constructor( domainSet: Collection<T>,
                 codomainSet: Collection<S>,
                 matrix: Array<Array<Int>> )
    : this( domainSet, codomainSet, Array(matrix.size) { row -> matrix[row].toList() }.asList() )

    /** Domain set of the relation */
    val domainSet: Set<T>

    /** Codomain set of the relation */
    val codomainSet: Set<S>

    init
    {
        // Set domain and codomain sets as immutable sets
        this.domainSet = domainSet.toSet()
        this.codomainSet = codomainSet.toSet()
    }


    /////////////
    // GETTERS
    /////////////

    /** Cardinal of the domain set */
    val domainCardinal = domainSet.size

    /** Cardinal of the codomain set */
    val codomainCardinal = codomainSet.size

    /** Domain set as list */
    val domainElements by lazy { domainSet.toList() }

    /** Codomain set as list */
    val codomainElements by lazy { codomainSet.toList() }

    var explicitMatrix: List<List<Int>>? = null

    /** Adjacency matrix ({0,1} matrix) */
    val matrix by lazy {
        explicitMatrix ?: Array( domainCardinal ) { row ->
            IntArray( codomainCardinal ) { col -> relation( domainElements[row], codomainElements[col] ).toInt }.asList()
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
    operator fun invoke( a: T, b: S ) = matrix[ this domainIndex a ][ this codomainIndex b ].toBool

    /**
     * Gets index of an element in the initial ordered set [domainElements]
     *
     * @param item element to get index
     * @return index of [item] in the initial ordered set [domainElements]
     */
    infix fun domainIndex( item: T ) = domainElements.indexOf(item)

    /**
     * Gets index of an element in the final ordered set [codomainElements]
     *
     * @param item element to get index
     * @return index of [item] in the final ordered set [codomainElements]
     */
    infix fun codomainIndex( item: S ) = codomainElements.indexOf(item)

    /**
     * Original set or preimage set (subset with all elements with at least an image)
     * >&emsp;__f^(R)={a&isin;A, &exist;b&isin;B, aRb}__
     */
    val preimage by lazy {
        mutableListOf<T>().apply {
            for ( row in matrix.indices )
                if ( !matrix[row].all { it == 0 } )
                    add( domainElements[row] )
        }.toSet()
    }

    /**
     * Image set (subset with all elements with at least an anti-image)
     * >&emsp;__f(R)={b&isin;B, &exist;a&isin;A, aRb}__
     */
    val image by lazy {
        mutableListOf<S>().apply {
            for ( col in 0 until codomainCardinal )
                if ( !IntArray(domainCardinal) { row -> matrix[row][col] }.all { it == 0 } )
                    add( codomainElements[col] )
        }.toSet()
    }

    /**
     * Gets elements related to given one which are in the second place of the pair
     * >&emsp;__{b&isin;B, aRb}__
     *
     * @param a prerelated element
     * @see preRelatedTo
     */
    infix fun postRelatedTo( a: T ) =
                                    domainIndex(a).let { codomainElements.filterIndexed { index, _ -> this[it,index] } }

    /**
     * Gets elements related to given one which are in the first place of the pair
     * >&emsp;__{a&isin;A, aRb}__
     *
     * @param b postrelated element
     * @see postRelatedTo
     */
    infix fun preRelatedTo( b: S ) =
                                    codomainIndex(b).let { domainElements.filterIndexed { index, _ -> this[index,it] } }


    ////////////////////////////////
    // PROPERTIES OF THE RELATION
    ////////////////////////////////

    /**>&emsp;__{&forall;a&isin;A, &exist;!b&isin;B, aRb}__ */
    val isApplication by lazy {
        for ( row in matrix )
            if ( row.count { it > 0 } != 1 )
                return@lazy false

        true
    }

    /**
     * >&emsp;__{&forall;a,b&isin;A, &forall;c&isin;B, aRc&and;bRc&rarr;a=b}__
     *
     * @see isBijective
     * @see isSurjective
     */
    val isInjective by lazy {
        for ( col in 0 until codomainCardinal )
            if ( IntArray(domainCardinal) { row -> matrix[row][col] }.count( Int::toBool ) > 1 )
                return@lazy false

        true
    }

    /**
     * >&emsp;__{&forall;b&isin;B, &exist;a&isin;A, aRb}__
     *
     * @see isBijective
     * @see isInjective
     */
    val isSurjective by lazy {
        for ( col in 0 until codomainCardinal )
            if ( IntArray(domainCardinal) { row -> matrix[row][col] }.all { it == 0 } )
                return@lazy false

        true
    }

    /**
     * Injective and surjective
     *
     * @see isInjective
     * @see isSurjective
     */
    val isBijective by lazy { isInjective && isSurjective }


    //////////////////////////////////
    // OPERATIONS BETWEEN RELATIONS
    //////////////////////////////////

    /**
     * Performs the union between two relation over the same sets
     * >&emsp;__R&cup;R'={(a,b)&isin;AxB, (a,b)&isin;R&or;(a,b)&isin;R'}__
     *
     * @param other another relation
     * @throws IllegalArgumentException if domain or codomain sets are not the same in both relations
     */
    infix fun union( other: Relation<T,S> ) =
        if ( other.domainSet != domainSet || other.codomainSet != codomainSet )
            throw IllegalArgumentException( "Domain and codomain sets must be the same in both relations" )
        else
            Relation( domainSet, codomainSet ) l@{ a, b ->
                val idxA = this@Relation domainIndex  a
                val idxB = this@Relation codomainIndex  b
                this@Relation[idxA,idxB] || other[idxA,idxB]
            }

    /** @see union */
    operator fun plus( other: Relation<T,S> ) = union( other )

    /**
     * Performs the intersection between two relation over the same sets
     * >&emsp;__R&cap;R'={(a,b)&isin;AxB, (a,b)&isin;R&and;(a,b)&isin;R'}__
     *
     * @param other another relation
     * @throws IllegalArgumentException if domain or codomain sets are not the same in both relations
     */
    infix fun intersection( other: Relation<T,S> ) =
        if ( other.domainSet != domainSet || other.codomainSet != codomainSet )
            throw IllegalArgumentException( "Domain and codomain sets must be the same in both relations" )
        else
            Relation( domainSet, codomainSet ) l@{ a, b ->
                val idxA = this@Relation domainIndex  a
                val idxB = this@Relation codomainIndex  b
                this@Relation[idxA,idxB] && other[idxA,idxB]
            }

    /** @see intersection */
    operator fun times( other: Relation<T,S> ) = intersection( other )

    /**
     * Performs the exclusive union between two relation over the same sets
     * >&emsp;__R&#8891;R'={(a,b)&isin;AxB, (a,b)&isin;R&#8891;(a,b)&isin;R'}__
     *
     * @param other another relation
     * @throws IllegalArgumentException if domain or codomain sets are not the same in both relations
     */
    infix fun xor( other: Relation<T,S> ) =
        if ( other.domainSet != domainSet || other.codomainSet != codomainSet )
            throw IllegalArgumentException( "Domain and codomain sets must be the same in both relations" )
        else
            Relation( domainSet, codomainSet ) l@{ a, b ->
                val idxA = this@Relation domainIndex  a
                val idxB = this@Relation codomainIndex  b
                this@Relation[idxA,idxB] xor other[idxA,idxB]
            }

    /**
     * Converse _[[transpose, inverse, dual, reciprocal, opposite]]_ relation
     * >&emsp;__Rt={(b,a)&isin;BxA, (a,b)&isin;R&sub;AxB}__
     */
    val converseRelation by lazy { Relation( codomainSet, domainSet ) l@{ a, b -> this@Relation( b, a ) } }

    /** @see converseRelation */
    operator fun unaryMinus() = converseRelation

    /** >&emsp;__R'={(a,b)&isin;AxB, (a,b)&notin;R&sub;AxB}__ */
    val complementaryRelation by lazy { Relation( domainSet, codomainSet ) l@{ a, b -> !this@Relation( a, b ) } }

    /** @see complementaryRelation */
    operator fun not() = complementaryRelation

    /**
     * Performs the composition f(g)
     *
     * @param other g in f(g)
     * @throws IllegalArgumentException if domain doesn't contain [other] image
     */
    infix fun <U> composition( other: Relation<U,T> ) =
        matrixBooleanProduct( other.matrix, matrix, codomainCardinal ).let {
            if ( !domainSet.containsAll( other.image ) )
                throw IllegalArgumentException( "Domain must contain [other] image" )

            Relation( other.domainSet, codomainSet ) { a, b -> it[other domainIndex a][this codomainIndex  b].toBool }
        }

    /** @see composition */
    operator fun <U> invoke( other: Relation<U,T> ) = composition( other )

    /**
     * Restriction of the relation to the given subset
     * >&emsp;__R/S={(a,b)&isin;SxB&sub;AxB, (a,b)&isin;R}__
     *
     * @param subset restriction subset of the domain set
     * @throws IllegalArgumentException [subset] must be contained in the domain set
     */
    fun restriction( subset: Set<T> ) =
        if ( !domainSet.containsAll( subset ) )
            throw IllegalArgumentException( "Not subset of domain set" )
        else
            Relation( subset, codomainSet ) l@{ a, b -> this@Relation(a,b) }

    /** @see restriction */
    operator fun div( subset: Set<T> ) = restriction( subset )


    /////////////////
    // CONVERSIONS
    /////////////////

    /**
     * Relation as endorelation
     *
     * @throws IllegalStateException if domain set and codomain set are not the same
     */
    val toEndoRelation by lazy {
        if ( domainSet == codomainSet )
            EndoRelation( domainSet, matrix )
        else
            throw IllegalStateException( "Domain set and codomain set must be the same" )
    }

    /**
     * Relation as a list of pairs of the cartesian product;
     * >&emsp;__[[(a,a),(a,c),(b,a),(b,d),...]]__
     */
    val asPairs by lazy {
        val pairs = mutableListOf<Pair<T,S>>()
        for ( row in matrix.indices )
            for ( col in 0 until codomainCardinal )
                if ( this[row,col] )
                    pairs.add( Pair( domainElements[row], codomainElements[col] ) )

        pairs.toList()
    }


    ////////////
    // OTHERS
    ////////////

    /** Compare __sets__ and __matrix__ to define relation equality */
    override fun equals( other: Any? ): Boolean
    {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as Relation<*, *>

        if (domainSet != other.domainSet) return false
        if (codomainSet != other.codomainSet) return false
        if (matrix != other.matrix) return false

        return true
    }

    override fun hashCode(): Int
    {
        var result = domainSet.hashCode()
        result = 31 * result + codomainSet.hashCode()
        result = 31 * result + matrix.hashCode()
        return result
    }

}  // class Relation
