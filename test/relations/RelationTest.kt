package relations

import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test

/**
 * @author Miguel Alejandro Moreno Barrientos, v0.1.0
 */
class RelationTest
{
    @Test
    @DisplayName("Generic")
    fun generic()
    {
        val rcubes = "cubes" rel Relation( IntRange(0,4).toSet(), setOf(0,1,8,27,64) ) { a,b -> a*a*a == b }
        val rchr = "chr" rel
                   Relation( setOf('a','b','c','d'), listOf('a','b','z').map { Character.getNumericValue(it) } ) { a,b ->
                       Character.getNumericValue(a) == b
                   }

        printRel( rcubes, rchr )

        assertAll(
            { assertTrue( rcubes.r.isApplication, rcubes.name ) },
            { assertTrue( rcubes.r.isBijective, rcubes.name ) },

            { assertFalse( rchr.r.isApplication, rchr.name ) },
            { assertFalse( rchr.r.isBijective, rchr.name ) },
            { assertEquals( setOf('a','b'), rchr.r.preimage, rchr.name ) },
            { assertEquals( setOf(10,11), rchr.r.image, rchr.name ) },
        )

        println( "postRelatedTo ${rcubes.name}:" )
        rcubes.r.domainSet.forEach { println( "$it -> ${rcubes.r postRelatedTo it}" ) }
        println( "preRelatedTo ${rcubes.name}:" )
        rcubes.r.codomainSet.forEach { println( "$it <- ${rcubes.r preRelatedTo it}" ) }

        assertAll (
            { assertEquals( listOf(64), rcubes.r postRelatedTo 4, rcubes.name ) },
            { assertEquals( listOf(3), rcubes.r preRelatedTo 27, rcubes.name ) },
        )
    }

    @Test
    @DisplayName("functions")
    fun functions()
    {
        val ff = "ff" rel Relation( setOf(0,1,2,3,4), setOf('a','b','c','d'), 0 to 'd', 1 to 'a' )
        val gg = "gg" rel Relation( setOf(0,1,2,3,4), setOf('a','b','c','d'), 0 to 'b', 4 to 'c' )
        val ffggor = "ffggor" rel ff.r + gg.r
        val ffggand = "ffggand" rel ff.r * gg.r
        val ffcomp = "ffcomp" rel !ff.r
        val ffconv = "ffconv" rel -ff.r
        val ffres = "ffres" rel ff.r / setOf( 0, 3 )

        printRel( ff, gg, ffggor, ffggand, ffcomp, ffconv, ffres )

        assertAll(
            { assertFalse( ffggor.r.isApplication, ffggor.name ) },
            { assertTrue( ffggor.r.isBijective, ffggor.name ) },
            { assertEquals( ff.r xor gg.r, ffggor.r, ffggor.name ) },

            { assertEquals( Relation( ffggand.r.domainSet, ffggand.r.codomainSet ), ffggand.r, ffggand.name ) },

            { assertEquals( ff.r, !ffcomp.r, ffcomp.name ) },

            { assertEquals( ff.r, -ffconv.r, ffconv.name ) },

            { assertEquals( setOf(0), ffres.r.preimage, ffres.name ) },
            { assertEquals( setOf('d'), ffres.r.image, ffres.name ) },
        )
    }

    @Test
    @DisplayName("f(g)")
    fun composition()
    {
        val f = Relation( setOf(1,2,3,4), setOf("Hi","world","!"), listOf(
            listOf( 0,0,0 ),
            listOf( 0,0,0 ),
            listOf( 0,1,0 ),
            listOf( 1,1,0 )
        ) )
        val g = Relation( setOf('a','b','c'),  setOf(1,2,3,4), listOf(
            listOf( 1,0,1,0 ),
            listOf( 0,0,0,0 ),
            listOf( 0,0,0,1 ),
        ) )
        val fg = "f(g)" rel f(g)

        printRel( fg )

        assertAll(
            { assertEquals( listOf( listOf(0,1,0), listOf(0,0,0), listOf(1,1,0) ), fg.r.matrix, fg.name ) },
            { assertEquals( setOf('a','c'), fg.r.preimage, fg.name ) },
            { assertEquals( setOf("Hi","world"), fg.r.image, fg.name ) },
        )

        val f2 = "f" rel Relation( setOf(-2.0,-1.0,0.0,1.0,2.0), setOf(-1.0,0.0,1.0,2.0,3.0,4.0) ) { x,y -> y == x + 1 }
        val g2 = "g" rel
                 Relation( setOf(-1.0,0.0,1.0,2.0,3.0,4.0), setOf(0.0,-1.0,0.0,3.0,8.0,15.0) ) { x,y -> y == x*x - 1 }
        val g2f2 = "g2(f2)" rel g2.r(f2.r)

        printRel( f2, g2, g2f2 )
    }

    @Test
    @DisplayName("Equality")
    fun equals()
    {
        assertEquals( Relation( setOf('a','c'), setOf(1,2) ) { a,b -> a.toInt() == b  },
                      Relation( setOf('a','c'), setOf(1,2) ) { a,b -> a.toInt() == b  } )
    }

    internal inner class RelInfo<T,S>( val name: String,
                                       val r: Relation<T,S> )

    private infix fun <T,S> String.rel( r: Relation<T,S> ) = RelInfo( this, r )

    private fun printRel( relInfo: RelInfo<*,*> )
    {
        println( "[[${relInfo.name}]]" )
        val rel = relInfo.r
        println( "${rel::domainCardinal.name}: ${rel.domainCardinal}" )
        println( "${rel::codomainCardinal.name}: ${rel.codomainCardinal}" )
        println( "${rel::domainElements.name}: ${rel.domainElements}" )
        println( "${rel::codomainElements.name}: ${rel.codomainElements}" )
        println( "${rel::preimage.name}: ${rel.preimage}" )
        println( "${rel::image.name}: ${rel.image}" )
        println( "${rel::matrix.name}:" )
        rel.matrix.forEach( ::println )
        println( "${rel::isApplication.name}: ${rel.isApplication}" )
        println( "${rel::isInjective.name}: ${rel.isInjective}" )
        println( "${rel::isSurjective.name}: ${rel.isSurjective}" )
        println( "${rel::isBijective.name}: ${rel.isBijective}" )
        println( "${rel::asPairs.name}: ${rel.asPairs}" )
        println()
    }

    private fun printRel( vararg args: RelInfo<*,*> ) = args.forEach { printRel( it ) }
}
