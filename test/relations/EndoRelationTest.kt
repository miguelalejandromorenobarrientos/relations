package relations

import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test
import kotlin.math.pow

/**
 * @author Miguel Alejandro Moreno Barrientos, v0.1.0
 */
internal class EndoRelationTest
{
    private val rm2 = "congruence mod 2" rel EndoRelation( IntRange( 0, 9 ).toSet() ) { a, b -> (b-a) % 2 == 0 }
    private val rm3 = "congruence mod 3" rel EndoRelation( IntRange( 0, 9 ).toSet() ) { a, b -> (b-a) % 3 == 0 }
    private val rm6 = "congruence mod 6" rel rm2.r * rm3.r  // (b-a) % 6 == 0
    private val rm2U3 = "union congruence mod 2 & 3" rel rm2.r + rm3.r  // (b-a) % 2 == 0 || (b-a) % 3 == 0
    private val rm2X3 = "xor congruence mod 2 & 3" rel (rm2.r xor rm3.r)  // (b-a) % 2 == 0 xor (b-a) % 3 == 0
    private val rm6not = "not congruence mod 6" rel !rm6.r  // (b-a) % 6 != 0
    private val rm6rest = "congruence mod 6 restricted" rel rm6.r / IntRange(2,8).toSet()
    private val rmmord = "multiplier or divider" rel
            ( EndoRelation( IntRange( 1, 8 ).toSet() ) { a, b -> a % b == 0 || b % a == 0 } +
              EndoRelation( IntRange( 1, 8 ).toSet() ) { a, b -> a % b == 0 || a % b == 0 } )  // intransitive
    private val rpar = "parity" rel EndoRelation( IntRange( 0, 9 ).toSet() ) { a, b -> a % 2 == b % 2 }  // evens and odds
    private val rid = "identity relation" rel EndoRelation( setOf( "a", "b", "c", "d" ) ) { a, b -> a == b }  // trivial relation
    private val r0 = "empty relation" rel EndoRelation( setOf( ' ', 'z', '\'', '$' ) ) { _, _ -> false }  // trivial relation
    private val r1 = "universal relation" rel EndoRelation( setOf( ' ', 'z', '\'', '$' ) ) { _, _ -> true }  // trivial relation
    private val rdiv = "divisibility" rel EndoRelation( IntRange( 1, 10 ).toSet() ) { a, b -> b % a == 0 }  // partial order
    private val rdiv2 = "divisibility from 2" rel EndoRelation( IntRange( 2, 10 ).toSet() ) { a, b -> b % a == 0 }  // partial order
    private val rlex = "string lexicographical order" rel
                       EndoRelation( setOf( "Hi!", "Zero", "Abigail", "Relation", "Z" ) ) { a, b -> a <= b }  // total order
    private val rnat = "naturals strict natural order" rel EndoRelation( IntRange(1,10).toSet() ) { a, b -> a < b }  // strict total order
    private val rsub = "subset not equal" rel EndoRelation( setOf( setOf(1,2), setOf(2), setOf(3,2), setOf(1,2,3) ) ) { a, b ->
        b.containsAll( a ) && b.size > a.size
    }  // strict total order
    private val rasym = "asymmetric from matrix" rel EndoRelation( IntRange( 1, 4 ).toSet(),
        listOf(
            listOf( 0, 0, 1, 0 ),
            listOf( 0, 0, 1, 0 ),
            listOf( 0, 0, 0, 0 ),
            listOf( 0, 1, 0, 0 ),
        ) )
    private val rtran = "transitive from matrix" rel EndoRelation( IntRange( 0, 3 ).toSet(),
        arrayOf(
            arrayOf( 0, 1, 0, 1 ),
            arrayOf( 0, 0, 0, 1 ),
            arrayOf( 1, 1, 0, 1 ),
            arrayOf( 0, 0, 0, 0 ),
        ) )
    private val rrsp = "rock, scissors, paper" rel EndoRelation( setOf( "ROCK", "SCISSORS", "PAPER" ),
        arrayOf(
            arrayOf( 0, 1, 0 ),
            arrayOf( 0, 0, 1 ),
            arrayOf( 1, 0, 0 ),
        ) )
    private val rcomp = "compose" rel ( EndoRelation( setOf('a','b'), 'a' to 'b', 'b' to 'a' ) composition
                                        EndoRelation( setOf('a','b'), 'a' to 'a', 'b' to 'a', 'b' to 'b' ) )
    private val rnatref = "strict natural order to not strict one by reflexive closure" rel rnat.r.reflexiveClosure  // total order from strict total order
    private val rdivsym = "div symmetric closure" rel rdiv.r.symmetricClosure  //


    @Test
    @DisplayName("Congruences")
    fun congruences()
    {
        printRel( rm2, rm3, rm6, rm2U3, rm2X3, rm6not, rm6rest )

        assertAll(
            { assertEquals( 10, rm2.r.cardinal, rm2.name ) },
            { assertTrue( rm2.r.isEquivalence, rm2.name ) },
            { assertFalse( rm2.r.isPartialOrder, rm2.name ) },
            { assertEquals( setOf( setOf(1,3,5,7,9), setOf(0,2,4,6,8) ), rm2.r.quotientSet ) },

            { assertTrue( rm3.r.isEquivalence, rm3.name ) },
            { assertFalse( rm3.r.isPartialOrder, rm3.name ) },

            { assertTrue( rm6.r.isEquivalence, rm6.name ) },
            { assertFalse( rm6.r.isPartialOrder, rm6.name ) },
            { assertEquals( setOf( setOf(0,6), setOf(2,8), setOf(3,9), setOf(1,7), setOf(5), setOf(4) ),
                            rm6.r.quotientSet ) },

            { assertFalse( rm2U3.r.isEquivalence, rm2U3.name ) },
            { assertFalse( rm2U3.r.isPartialOrder, rm2U3.name ) },

            { assertEquals( listOf(0,1,2,4,5,6,7,8), rm6not.r preRelatedTo 9, rm6not.name ) },

            { assertEquals( 6, rm6rest.r.quotientSet.size, rm6rest.name ) },
        )
    }

    @Test
    @DisplayName("Equivalences")
    fun equivalences()
    {
        printRel( rpar )

        assertAll(
            { assertTrue( rpar.r.isEquivalence, rpar.name ) },
            { assertEquals( setOf( (1..9 step 2).toSet(), (0..8 step 2).toSet() ),
                            rpar.r.quotientSet, rpar.name ) },
        )
    }

    @Test
    @DisplayName("Partial orders")
    fun partialOrders()
    {
        printRel( rdiv, rdiv2, rsub, rnat )

        assertAll(
            { assertTrue( rdiv.r.isPartialOrder, rdiv.name ) },
            { assertFalse( rdiv.r.isStrictPartialOrder, rdiv.name ) },
            { assertFalse( rdiv.r.isTotalOrder, rdiv.name ) },
            { assertFalse( rdiv.r.isStrictTotalOrder, rdiv.name ) },
            { assertEquals( 1, rdiv.r.minimum, rdiv.name ) },
            { assertNull( rdiv.r.maximum, rdiv.name ) },
            { assertEquals( setOf(10,9,8,7,6), rdiv.r.maximals.toSet(), rdiv.name ) },

            { assertTrue( rdiv2.r.isPartialOrder, rdiv2.name ) },
            { assertFalse( rdiv2.r.isStrictPartialOrder, rdiv2.name ) },
            { assertFalse( rdiv2.r.isTotalOrder, rdiv2.name ) },
            { assertFalse( rdiv2.r.isStrictTotalOrder, rdiv2.name ) },
            { assertEquals( setOf(2,3,5,7), rdiv2.r.minimals.toSet(), rdiv2.name ) },  // primes
            { assertEquals( setOf(6,7,8,9,10), rdiv2.r.maximals.toSet(), rdiv2.name ) },

            { assertFalse( rsub.r.isPartialOrder, rsub.name ) },
            { assertTrue( rsub.r.isStrictPartialOrder, rsub.name ) },
            { assertFalse( rsub.r.isTotalOrder, rsub.name ) },
            { assertFalse( rsub.r.isStrictTotalOrder, rsub.name ) },
            { assertEquals( setOf(2), rsub.r.minimum, rsub.name ) },
            { assertEquals( setOf(3,2,1), rsub.r.maximum, rsub.name ) },

            { assertFalse( rnat.r.isTotalOrder, rnat.name ) },
            { assertTrue( rnat.r.isStrictTotalOrder, rnat.name ) },
            { assertEquals( 1, rnat.r.minimum, rnat.name ) },
            { assertEquals( 10, rnat.r.maximum, rnat.name ) },
            { assertTrue( rnat.r.isBoundedAbove, rnat.name ) },
        )
    }

    @Test
    @DisplayName("Total orders")
    fun totalOrders()
    {
        printRel( rlex, rnatref )

        assertAll(
            { assertTrue( rlex.r.isTotalOrder, rlex.name ) },
            { assertFalse( rlex.r.isStrictTotalOrder, rlex.name ) },
            { assertEquals( "Abigail", rlex.r.minimum, rlex.name ) },
            { assertEquals( "Zero", rlex.r.maximum, rlex.name ) },
            { assertTrue( rlex.r.isBoundedAbove, rlex.name ) },

            { assertTrue( rnatref.r.isTotalOrder, rnatref.name ) },
            { assertFalse( rnatref.r.isStrictTotalOrder, rnatref.name ) },
            { assertEquals( 1, rnat.r.minimum, rnat.name ) },
            { assertEquals( 10, rnat.r.maximum, rnat.name ) },
            { assertTrue( rnat.r.isBoundedAbove, rnat.name ) },
        )
    }

    @Test
    @DisplayName("Trivial relations")
    fun trivial()
    {
        printRel( r0, r1, rid )

        assertAll(
            { assertTrue( r0.r.isIrreflexive, r0.name ) },
            { assertTrue( r0.r.isAsymmetric, r0.name ) },
            { assertTrue( r0.r.isSymmetric, r0.name ) },
            { assertTrue( r0.r.isAntisymmetric, r0.name ) },
            { assertTrue( r0.r.isStrictPartialOrder, r0.name ) },
            { assertTrue( r0.r.isTransitive, r0.name ) },
            { assertTrue( r0.r.asPairs.isEmpty(), r0.name ) },

            { assertTrue( r1.r.isEquivalence, r1.name ) },
            { assertEquals( 2.0.pow(r1.r.cardinal).toInt(), r1.r.asPairs.size, r1.name ) },

            { assertTrue( rid.r.isEquivalence, rid.name ) },
            { assertTrue( rid.r.isPartialOrder, rid.name ) },
            { assertEquals( listOf( "a" to "a", "b" to "b", "c" to "c", "d" to "d" ),
                            rid.r.asPairs, rid.name ) },
            { assertEquals( listOf("a","b","c","d"), rid.r.minimals, rid.name ) },
            { assertEquals( rid.r.maximals, rid.r.minimals, rid.name ) },
        )
    }

    @Test
    @DisplayName("From matrix")
    fun fromMatrix()
    {
        printRel( rasym, rtran, rrsp )

        assertAll(
            { assertTrue( rasym.r.isAsymmetric, rasym.name ) },
            { assertTrue( rasym.r.isAntisymmetric, rasym.name ) },

            { assertTrue( rtran.r.isTransitive, rtran.name ) },

            { assertFalse( rrsp.r.isTransitive, rrsp.name ) },
            { assertTrue( rrsp.r.isAntitransitive, rrsp.name ) },
            { assertTrue( rrsp.r.isIntransitive, rrsp.name ) },
            { assertTrue( rrsp.r.isCircular, rrsp.name ) },
            { assertTrue( rrsp.r.isApplication, rrsp.name ) },
        )
    }

    @Test
    @DisplayName("From pairs")
    fun fromPairs()
    {
        printRel( rcomp )

        assertAll(
            { assertEquals( listOf( listOf(1,1), listOf(1,0) ), rcomp.r.matrix, rcomp.name ) },
            { assertEquals( listOf('a','b'), rcomp.r postRelatedTo 'a', rcomp.name ) },
            { assertEquals( listOf('a'), rcomp.r postRelatedTo 'b', rcomp.name ) },
            { assertEquals( listOf('a','b'), rcomp.r preRelatedTo 'a', rcomp.name ) },
            { assertEquals( listOf('a'), rcomp.r preRelatedTo 'b', rcomp.name ) },
        )
    }

    @Test
    @DisplayName("Generic")
    fun generic()
    {
        printRel( rmmord, rdivsym )

        assertAll(
            { assertTrue( rmmord.r.isIntransitive, rmmord.name ) },
            { assertEquals( EndoRelation( IntRange( 1, 8 ).toSet() ) { a, b -> a % b == 0 || b % a == 0 }.matrix,
                rmmord.r.matrix, rmmord.name ) },

            { assertTrue( rdivsym.r.isSymmetric, rdivsym.name ) },
        )
    }

    @Test
    @DisplayName("Equality")
    fun equals()
    {
        assertEquals( EndoRelation( setOf('a','c') ) { a,b -> a == b  },
                      EndoRelation( setOf('c','a') ) { a,b -> a == b  } )
    }

    internal inner class RelInfo<T>( val name: String,
                                     val r: EndoRelation<T> )

    private infix fun <T> String.rel( r: EndoRelation<T> ) = RelInfo( this, r )

    private fun printRel( relInfo: RelInfo<*> )
    {
        println( "[[${relInfo.name}]]" )
        val rel = relInfo.r
        println( "${rel::cardinal.name}: ${rel.cardinal}" )
        println( "${rel::elements.name}: ${rel.elements}" )
        println( "${rel::preimage.name}: ${rel.preimage}" )
        println( "${rel::image.name}: ${rel.image}" )
        println( "${rel::matrix.name}:" )
        rel.matrix.forEach( ::println )
        println( "${rel::isApplication.name}: ${rel.isApplication}" )
        println( "${rel::isInjective.name}: ${rel.isInjective}" )
        println( "${rel::isSurjective.name}: ${rel.isSurjective}" )
        println( "${rel::isBijective.name}: ${rel.isBijective}" )
        println( "${rel::isReflexive.name}: ${rel.isReflexive}" )
        println( "${rel::isIrreflexive.name}: ${rel.isIrreflexive}" )
        println( "${rel::isSymmetric.name}: ${rel.isSymmetric}" )
        println( "${rel::isAsymmetric.name}: ${rel.isAsymmetric}" )
        println( "${rel::isAntisymmetric.name}: ${rel.isAntisymmetric}" )
        println( "${rel::isTransitive.name}: ${rel.isTransitive}" )
        println( "${rel::isIntransitive.name}: ${rel.isIntransitive}" )
        println( "${rel::isAntitransitive.name}: ${rel.isAntitransitive}" )
        println( "${rel::isCircular.name}: ${rel.isCircular}" )
        println( "${rel::isConnected.name}: ${rel.isConnected}" )
        println( "${rel::isTotal.name}: ${rel.isTotal}" )
        println( "${rel::isDependency.name}: ${rel.isDependency}" )
        println( "${rel::isPreorder.name}: ${rel.isPreorder}" )
        println( "${rel::isPartialOrder.name}: ${rel.isPartialOrder}" )
        println( "${rel::isTotalOrder.name}: ${rel.isTotalOrder}" )
        println( "${rel::isStrictPartialOrder.name}: ${rel.isStrictPartialOrder}" )
        println( "${rel::isStrictTotalOrder.name}: ${rel.isStrictTotalOrder}" )
        println( "${rel::isEquivalence.name}: ${rel.isEquivalence}" )
        if ( rel.isPartialOrder || rel.isStrictPartialOrder )
        {
            println( "${rel::isBoundedAbove.name}: ${rel.isBoundedAbove}" )
            println( "${rel::isBoundedBelow.name}: ${rel.isBoundedBelow}" )
            println( "${rel::isBounded.name}: ${rel.isBounded}" )
            println("${rel::minimals.name}: ${rel.minimals}")
            println("${rel::maximals.name}: ${rel.maximals}")
            println("${rel::minimum.name}: ${rel.minimum}")
            println("${rel::maximum.name}: ${rel.maximum}")
        }
        if ( rel.isEquivalence )
        {
            println( "${rel::quotientSet.name}: ${rel.quotientSet}" )
            println( "${rel::quotientSet.name} cardinal: ${rel.quotientSet.size}" )
        }
        println( "${rel::asPairs.name}: ${rel.asPairs}" )
        println()
    }

    private fun printRel(vararg args: RelInfo<*> ) = args.forEach { printRel( it ) }
}
