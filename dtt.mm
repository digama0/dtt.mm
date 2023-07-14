$( dtt.mm  25-Feb-2016 $)

$(
                      PUBLIC DOMAIN DEDICATION

This file is placed in the public domain per the Creative Commons Public
Domain Dedication. http://creativecommons.org/licenses/publicdomain/

Mario Carneiro - email: di.gama at gmail.com

$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                           Foundations
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $( Declare the primitive constant symbols for lambda calculus. $)
  $c set $.   $( Typecode for variables (syntax) $)
  $c term $.  $( Typecode for terms (syntax) $)
  $c oterm $. $( Typecode for open terms (syntax) $)
  $c mterm $. $( Typecode for middle terms (syntax) $)
  $c wff $.   $( Typecode for deductions (syntax). $)
  $c |- $.    $( Typecode for theorems (logical) $)
  $c : $.     $( Typehood indicator $)
  $c := $.    $( Definitional equality $)
  $c |= $.    $( Context separator $)
  $c , $.     $( Separator $)
  $c ( $.     $( Open parenthesis $)
  $c ) $.     $( Close parenthesis $)
  $c \ $.     $( Lambda expression $)
  $c T. $.    $( Truth wff $)

  $v x y z f g p q $.  $( Bound variables $)
  $v A B C D F R S T $.  $( Term variables $)
  $v ph ps ch th $.  $( Wff variables $)
  $v OA OB OC OD OE MA MB $.  $( Special variables $)

  $( Let variable ` ph ` be a wff. $)
  wph $f wff ph $.
  $( Let variable ` ps ` be a wff. $)
  wps $f wff ps $.
  $( Let variable ` ch ` be a wff. $)
  wch $f wff ch $.
  $( Let variable ` th ` be a wff. $)
  wth $f wff th $.

  $( Let variable ` A ` be a term. $)
  tA $f term A $.
  $( Let variable ` B ` be a term. $)
  tB $f term B $.
  $( Let variable ` C ` be a term. $)
  tC $f term C $.
  $( Let variable ` D ` be a term. $)
  tD $f term D $.
  $( Let variable ` F ` be a term. $)
  tF $f term F $.
  $( Let variable ` R ` be a term. $)
  tR $f term R $.
  $( Let variable ` S ` be a term. $)
  tS $f term S $.
  $( Let variable ` T ` be a term. $)
  tT $f term T $.

  $( Let variable ` OA ` be an open term. $)
  oA $f oterm OA $.
  $( Let variable ` OB ` be an open term. $)
  oB $f oterm OB $.
  $( Let variable ` OC ` be an open term. $)
  oC $f oterm OC $.
  $( Let variable ` OD ` be an open term. $)
  oD $f oterm OD $.
  $( Let variable ` OE ` be an open term. $)
  oE $f oterm OE $.

  $( Let variable ` MA ` be a middle term. $)
  mA $f mterm MA $.
  $( Let variable ` MB ` be a middle term. $)
  mB $f mterm MB $.

  $( Let variable ` x ` be a set variable. $)
  vx $f set x $.
  $( Let variable ` y ` be a set variable. $)
  vy $f set y $.
  $( Let variable ` z ` be a set variable. $)
  vz $f set z $.
  $( Let variable ` f ` be a set variable. $)
  vf $f set f $.
  $( Let variable ` g ` be a set variable. $)
  vg $f set g $.
  $( Let variable ` p ` be a set variable. $)
  vp $f set p $.
  $( Let variable ` q ` be a set variable. $)
  vq $f set q $.

  $( A set is a term.
       (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  tv $a term x $.
  $( A term is a middle term.
       (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  mt $a mterm A $.
  $( A middle term is an open term.
       (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  om $a oterm MA $.
  $( An open term with parentheses is a term.
       (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  to $a term ( OA ) $.

  $( A combination (function application). Middle terms are used for ensuring
     left-associativity of combination, with higher precedence than lambda
     abstraction.
       (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  mc $a mterm MA B $.
  $( A lambda abstraction is a term.
       (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  ol $a oterm \ x : OA , OB $.

  $( Typehood assertion.
       (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  wk $a wff OA : OB $.
  $( Definitional equality.
       (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  wde $a wff OA := OB $.
  $( Context operator.
       (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  wa $a wff ( ph , ps ) $.
  $( A deduction is a wff.
       (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  wi $a wff ( ph |= ps ) $.
  $( Tautology is a wff.
       (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  wtru $a wff T. $.

  ${
    idi.1 $e |- ph $.
    $( The identity inference.
       (Contributed by Mario Carneiro, 25-Feb-2016.) $)
    idi $p |- ph $=
      (  ) B $.
      $( [25-Feb-2016] $)
  $}

  $( Axiom _Simp_.
       (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  ax-1 $a |- ( ph |= ( ps |= ph ) ) $.

  $( Axiom _Frege_.
       (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  ax-2 $a |- ( ( ph |= ( ps |= ch ) ) |= ( ( ph |= ps ) |= ( ph |= ch ) ) ) $.

  ${
    $( Minor premise for modus ponens. $)
    min $e |- ph $.
    $( Major premise for modus ponens. $)
    maj $e |- ( ph |= ps ) $.
    $( Rule of Modus Ponens.
       (Contributed by Mario Carneiro, 25-Feb-2016.) $)
    ax-mp $a |- ps $.
  $}

  ${
    a1i.1 $e |- ph $.
    $( Change an empty context into any context.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    a1i $p |- ( ps |= ph ) $=
      ( wi ax-1 ax-mp ) ABADCABEF $.
      $( [26-Feb-2016] $)
  $}

  ${
    mpd.1 $e |- ( ph |= ps ) $.
    mpd.2 $e |- ( ph |= ( ps |= ch ) ) $.
    $( Modus ponens deduction.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    mpd $p |- ( ph |= ch ) $=
      ( wi ax-2 ax-mp ) ABFZACFZDABCFFIJFEABCGHH $.
      $( [26-Feb-2016] $)
  $}

  ${
    syl.1 $e |- ( ph |= ps ) $.
    syl.2 $e |- ( ps |= ch ) $.
    $( Syllogism inference.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    syl $p |- ( ph |= ch ) $=
      ( wi a1i mpd ) ABCDBCFAEGH $.
      $( [26-Feb-2016] $)
  $}

  $( The identity inference.
     (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  id $p |- ( ph |= ph ) $=
    ( wi ax-1 mpd ) AAABZAAACAECD $.
    $( [26-Feb-2016] $)

  ${
    ax-imp.1 $e |- ( ph |= ( ps |= ch ) ) $.
    $( Importation for context conjunction.
       (Contributed by Mario Carneiro, 25-Feb-2016.) $)
    ax-imp $a |- ( ( ph , ps ) |= ch ) $.

    $( Importation for context conjunction.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    imp $p |- ( ( ph , ps ) |= ch ) $=
      ( ax-imp ) ABCDE $.
      $( [26-Feb-2016] $)
  $}

  ${
    ax-ex.1 $e |- ( ( ph , ps ) |= ch ) $.
    $( Exportation for context conjunction.
       (Contributed by Mario Carneiro, 25-Feb-2016.) $)
    ax-ex $a |- ( ph |= ( ps |= ch ) ) $.

    $( Exportation for context conjunction.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    ex $p |- ( ph |= ( ps |= ch ) ) $=
      ( ax-ex ) ABCDE $.
      $( [26-Feb-2016] $)
  $}

  ${
    jca.1 $e |- ( ph |= ps ) $.
    jca.2 $e |- ( ph |= ch ) $.
    $( Syllogism inference.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    jca $p |- ( ph |= ( ps , ch ) ) $=
      ( wa wi id ex syl mpd ) ACBCFZEABCLGDBCLLHIJK $.
      $( [26-Feb-2016] $)
  $}

  ${
    syl2anc.1 $e |- ( ph |= ps ) $.
    syl2anc.2 $e |- ( ph |= ch ) $.
    syl2anc.3 $e |- ( ( ps , ch ) |= th ) $.
    $( Syllogism inference.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    syl2anc $p |- ( ph |= th ) $=
      ( wa jca syl ) ABCHDABCEFIGJ $.
      $( [26-Feb-2016] $)
  $}

  ${
    mp2an.1 $e |- ph $.
    mp2an.2 $e |- ps $.
    mp2an.3 $e |- ( ( ph , ps ) |= ch ) $.
    $( An inference based on modus ponens.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    mp2an $p |- ch $=
      ( a1i syl2anc ax-mp ) ACDAABCAADGBAEGFHI $.
      $( [26-Feb-2016] $)
  $}

  $( Extract an assumption from the context.
     (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  simpl $p |- ( ( ph , ps ) |= ph ) $=
    ( ax-1 imp ) ABAABCD $.
    $( [26-Feb-2016] $)

  $( Extract an assumption from the context.
     (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  simpr $p |- ( ( ph , ps ) |= ps ) $=
    ( wi id a1i imp ) ABBBBCABDEF $.
    $( [26-Feb-2016] $)

  $( "Definition" of tautology.
     (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  ax-tru $a |- T. $.

  $( Tautology is provable.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  tru $p |- T. $=
    ( ax-tru ) A $.
    $( [26-Feb-2016] $)

  ${
    trud.1 $e |- ( T. |= ph ) $.
    $( Eliminate ` T. ` as an antecedent.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    trud $p |- ph $=
      ( wtru tru ax-mp ) CADBE $.
      $( [26-Feb-2016] $)
  $}

  ${
    mpdan.1 $e |- ( ph |= ps ) $.
    mpdan.2 $e |- ( ( ph , ps ) |= ch ) $.
    $( Modus ponens deduction.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    mpdan $p |- ( ph |= ch ) $=
      ( ex mpd ) ABCDABCEFG $.
      $( [26-Feb-2016] $)
  $}

  ${
    simpld.1 $e |- ( ph |= ( ps , ch ) ) $.
    $( Extract an assumption from the context.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    simpld $p |- ( ph |= ps ) $=
      ( wa simpl syl ) ABCEBDBCFG $.
      $( [26-Feb-2016] $)

    $( Extract an assumption from the context.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    simprd $p |- ( ph |= ch ) $=
      ( wa simpr syl ) ABCECDBCFG $.
      $( [26-Feb-2016] $)
  $}

  ${
    ancoms.1 $e |- ( ( ph , ps ) |= ch ) $.
    $( Swap the two elements of a context.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    ancoms $p |- ( ( ps , ph ) |= ch ) $=
      ( wa simpr simpl syl2anc ) BAEABCBAFBAGDH $.
      $( [26-Feb-2016] $)
  $}

  ${
    adantr.1 $e |- ( ph |= ch ) $.
    $( Extract an assumption from the context.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    adantr $p |- ( ( ph , ps ) |= ch ) $=
      ( wa simpl syl ) ABEACABFDG $.
      $( [26-Feb-2016] $)

    $( Extract an assumption from the context.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    adantl $p |- ( ( ps , ph ) |= ch ) $=
      ( adantr ancoms ) ABCABCDEF $.
      $( [26-Feb-2016] $)
  $}

  ${
    anim2i.1 $e |- ( ph |= ps ) $.
    $( Introduce a right conjunct.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    anim1i $p |- ( ( ph , ch ) |= ( ps , ch ) ) $=
      ( wa adantr simpr jca ) ACEBCACBDFACGH $.
      $( [26-Feb-2016] $)

    $( Introduce a left conjunct.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    anim2i $p |- ( ( ch , ph ) |= ( ch , ps ) ) $=
      ( wa simpl adantl jca ) CAECBCAFACBDGH $.
      $( [26-Feb-2016] $)
  $}

  ${
    syldan.1 $e |- ( ( ph , ps ) |= ch ) $.
    syldan.2 $e |- ( ( ph , ch ) |= th ) $.
    $( Syllogism inference.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    syldan $p |- ( ( ph , ps ) |= th ) $=
      ( wa simpl syl2anc ) ABGACDABHEFI $.
      $( [26-Feb-2016] $)
  $}

  ${
    sylan.1 $e |- ( ph |= ps ) $.
    sylan.2 $e |- ( ( ps , ch ) |= th ) $.
    $( Syllogism inference.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    sylan $p |- ( ( ph , ch ) |= th ) $=
      ( wa anim1i syl ) ACGBCGDABCEHFI $.
      $( [26-Feb-2016] $)
  $}

  ${
    an32s.1 $e |- ( ( ( ph , ps ) , ch ) |= th ) $.
    $( Commutation identity for context.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    an32s $p |- ( ( ( ph , ch ) , ps ) |= th ) $=
      ( wa simpl anim1i simpr adantr syl2anc ) ACFZBFABFCDLABACGHLBCACIJEK $.
      $( [26-Feb-2016] $)

    $( Associativity for context.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    anasss $p |- ( ( ph , ( ps , ch ) ) |= th ) $=
      ( wa id ancoms sylan an32s ) BCFADBACDBAFABFZCDABKKGHEIJH $.
      $( [26-Feb-2016] $)
  $}

  ${
    anassrs.1 $e |- ( ( ph , ( ps , ch ) ) |= th ) $.
    $( Associativity for context.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    anassrs $p |- ( ( ( ph , ps ) , ch ) |= th ) $=
      ( wa simpl adantr simpr anim1i syl2anc ) ABFZCFABCFDLCAABGHLBCABIJEK $.
      $( [26-Feb-2016] $)
  $}

  $( Reflexivity of equality.
       (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  ax-deid $a |- OA := OA $.

  $( Reflexivity of equality.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  deid $p |- OA := OA $=
    ( ax-deid ) AB $.
    $( [26-Feb-2016] $)

  $( Reflexivity of equality.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  deidd $p |- ( ph |= OA := OA ) $=
    ( wde deid a1i ) BBCABDE $.
    $( [26-Feb-2016] $)

  $( Transitivity of equality.
       (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  ax-detr $a |- ( ( OA := OB , OC := OB ) |= OA := OC ) $.

  ${
    $( Symmetry of equality.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    desym $p |- ( OA := OB |= OB := OA ) $=
      ( wde deidd id ax-detr syl2anc ) ABCZBBCHBACHBDHEBBAFG $.
      $( [26-Feb-2016] $)
  $}

  ${
    desymi.1 $e |- OA := OB $.
    $( Symmetry of equality.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    desymi $p |- OB := OA $=
      ( wde desym ax-mp ) ABDBADCABEF $.
      $( [26-Feb-2016] $)

    ${
      desymi.2 $e |- OC := OB $.
      $( Transitivity of equality.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
      detr4i $p |- OA := OC $=
        ( wde ax-detr mp2an ) ABFCBFACFDEABCGH $.
        $( [26-Feb-2016] $)
    $}

    detri.2 $e |- OB := OC $.
    $( Transitivity of equality.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    detri $p |- OA := OC $=
      ( desymi detr4i ) ABCDBCEFG $.
      $( [26-Feb-2016] $)
  $}

  ${
    desymd.1 $e |- ( ph |= OA := OB ) $.
    $( Symmetry of equality.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    desymd $p |- ( ph |= OB := OA ) $=
      ( wde desym syl ) ABCECBEDBCFG $.
      $( [26-Feb-2016] $)

    ${
      desymd.2 $e |- ( ph |= OC := OB ) $.
      $( Transitivity of equality.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
      detr4d $p |- ( ph |= OA := OC ) $=
        ( wde ax-detr syl2anc ) ABCGDCGBDGEFBCDHI $.
        $( [26-Feb-2016] $)
    $}

    detrd.2 $e |- ( ph |= OB := OC ) $.
    $( Transitivity of equality.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    detrd $p |- ( ph |= OA := OC ) $=
      ( desymd detr4d ) ABCDEACDFGH $.
      $( [26-Feb-2016] $)
  $}

  ${
    3detr4d.1 $e |- ( ph |= OA := OB ) $.
    ${
      3detr4d.2 $e |- ( ph |= OC := OA ) $.
      3detr4d.3 $e |- ( ph |= OD := OB ) $.
      $( Transitivity of equality.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
      3detr4d $p |- ( ph |= OC := OD ) $=
        ( detr4d ) ADBEGAECBHFII $.
        $( [26-Feb-2016] $)
    $}

    ${
      3detr3d.2 $e |- ( ph |= OA := OC ) $.
      3detr3d.3 $e |- ( ph |= OB := OD ) $.
      $( Transitivity of equality.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
      3detr3d $p |- ( ph |= OC := OD ) $=
        ( desymd detrd ) ADCEADBCABDGIFJHJ $.
        $( [26-Feb-2016] $)
    $}

    ${
      3detr4g.2 $e |- OC := OA $.
      3detr4g.3 $e |- OD := OB $.
      $( Transitivity of equality.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
      3detr4g $p |- ( ph |= OC := OD ) $=
        ( wde a1i 3detr4d ) ABCDEFDBIAGJECIAHJK $.
        $( [26-Feb-2016] $)
    $}

    ${
      3detr3g.2 $e |- OA := OC $.
      3detr3g.3 $e |- OB := OD $.
      $( Transitivity of equality.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
      3detr3g $p |- ( ph |= OC := OD ) $=
        ( wde a1i 3detr3d ) ABCDEFBDIAGJCEIAHJK $.
        $( [26-Feb-2016] $)
    $}
  $}

  $( Definitional equality applied to a typehood assertion.
       (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  ax-dek $a |- ( ( OA := OB , OC := OD ) |= ( OA : OC |= OB : OD ) ) $.

  $( Reduction of parentheses.
       (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  df-b $a |- ( OA ) := OA $.

  $( Equality theorem for parentheses.
   (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  bd $p |- ( ph |= ( OA ) := OA ) $=
    ( to mt om wde df-b a1i ) BCDEBFABGH $.
    $( [26-Feb-2016] $)

  ${
    bded.1 $e |- ( ph |= OA := OB ) $.
    $( Equality theorem for parentheses.
     (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    bded $p |- ( ph |= ( OA ) := ( OB ) ) $=
      ( to mt om df-b 3detr4g ) ABCBEFGCEFGDBHCHI $.
      $( [26-Feb-2016] $)
  $}

  ${
    dektri.1 $e |- OA := OB $.
    dektri.2 $e |- OB : OC $.
    $( Substitution of equal classes into membership relation.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    dektri $p |- OA : OC $=
      ( wk wde wi desymi ax-deid ax-dek mp2an ax-mp ) BCFZACFZEBAGCCGNOHABDICJB
      ACCKLM $.
      $( [26-Feb-2016] $)
  $}

  ${
    kdetri.1 $e |- OA : OB $.
    kdetri.2 $e |- OB := OC $.
    $( Substitution of equal classes into membership relation.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    kdetri $p |- OA : OC $=
      ( wk wde wi deid ax-dek mp2an ax-mp ) ABFZACFZDAAGBCGMNHAIEAABCJKL $.
      $( [26-Feb-2016] $)
  $}

  ${
    dektrd.1 $e |- ( ph |= OA := OB ) $.
    dektrd.2 $e |- ( ph |= OB : OC ) $.
    $( Substitution of equal classes into membership relation.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    dektrd $p |- ( ph |= OA : OC ) $=
      ( wk wde wi desymd deidd ax-dek syl2anc mpd ) ACDGZBDGZFACBHDDHOPIABCEJAD
      KCBDDLMN $.
      $( [26-Feb-2016] $)
  $}

  ${
    kdetrd.1 $e |- ( ph |= OA : OB ) $.
    kdetrd.2 $e |- ( ph |= OB := OC ) $.
    $( Substitution of equal classes into membership relation.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    kdetrd $p |- ( ph |= OA : OC ) $=
      ( wk wde wi deidd ax-dek syl2anc mpd ) ABCGZBDGZEABBHCDHNOIABJFBBCDKLM $.
      $( [26-Feb-2016] $)
  $}

  $( The type of a combination.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  ax-kc $a |- ( ( MA : \ x : A , OB , B : A ) |= MA B : MB B ) $.

  $( Equality theorem for a combination.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  ax-cde $a |- ( ( MA := MB , A := B ) |= MA A := MB B ) $.

  ${
    kcd.1 $e |- ( ph |= MA : \ x : A , OB ) $.
    kcd.2 $e |- ( ph |= B : A ) $.
    $( The type of a combination.
     (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    kcd $p |- ( ph |= MA B : MB B ) $=
      ( om mt ol wk mc ax-kc syl2anc ) AEJBKJZDGLMCKJQMCENJCFNJMHIBCDEFGOP $.
      $( [26-Feb-2016] $)
  $}

  ${
    cde12d.1 $e |- ( ph |= MA := MB ) $.
    ${
      cde12d.2 $e |- ( ph |= A := B ) $.
      $( Equality theorem for combination.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
      cde12d $p |- ( ph |= MA A := MB B ) $=
        ( om wde mt mc ax-cde syl2anc ) ADHEHIBJHCJHIBDKHCEKHIFGBCDELM $.
        $( [26-Feb-2016] $)
    $}

    $( Equality theorem for combination.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    cde1d $p |- ( ph |= MA A := MB A ) $=
      ( mt om deidd cde12d ) ABBCDEABFGHI $.
      $( [26-Feb-2016] $)
  $}

  ${
    cde2d.1 $e |- ( ph |= A := B ) $.
    $( Equality theorem for combination.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    cde2d $p |- ( ph |= MA A := MA B ) $=
      ( om deidd cde12d ) ABCDDADFGEH $.
      $( [26-Feb-2016] $)
  $}

  $( Equality theorem for a lambda abstraction.
   (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  ax-lde1 $a |- ( OA := OB |= \ x : OA , OC := \ x : OB , OC ) $.

  ${
    lde1d.1 $e |- ( ph |= OA := OB ) $.
    $( Equality theorem for a lambda abstraction.
     (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    lde1d $p |- ( ph |= \ x : OA , OC := \ x : OB , OC ) $=
      ( wde ol ax-lde1 syl ) ABCGBDEHCDEHGFBCDEIJ $.
      $( [26-Feb-2016] $)
  $}

  ${
    $d x ph $.
    ${
      ax-kl.1 $e |- ( ph |= OA : OD ) $.
      ax-kl.2 $e |- ( ( ph , x : OA ) |= OB : OC ) $.
      $( The type of a lambda abstraction.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
      ax-kl $a |- ( ph |= \ x : OA , OB : \ x : OA , OC ) $.
    $}

    ${
      ax-lde.2 $e |- ( ( ph , x : OA ) |= OB := OC ) $.
      $( Equality theorem for a lambda abstraction.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
      ax-lde $a |- ( ph |= \ x : OA , OB := \ x : OA , OC ) $.
    $}

    ${
      lded.1 $e |- ( ph |= OB := OC ) $.
      $( Equality theorem for a lambda abstraction.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
      lded $p |- ( ph |= \ x : OA , OB := \ x : OA , OC ) $=
        ( tv mt om wk wde adantr ax-lde ) ABCDEAEGHIBJCDKFLM $.
        $( [26-Feb-2016] $)
    $}
  $}

  $( Axiom of eta reduction.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  ax-eta $a |- ( MB : \ y : OA , OC |= \ x : OA , MB x := MB ) $.

  $( Distribution of combination over substitution.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  ax-distrc $a |- ( \ x : OA , MA B ) A :=
                  ( \ x : OA , MA ) A ( ( \ x : OA , B ) A ) $.

  ${
    $d x y $.  $d y A $.
    $( Distribution of lambda abstraction over substitution.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    ax-distrl $a |- ( \ x : OA , \ y : OB , OC ) A :=
                    \ y : ( \ x : OA , OB ) A , ( \ x : OA , OC ) A $.
  $}

  $( ` x ` is bound in ` \ x , A ` , $)
  ax-hbl1 $a |- ( A : OA |=
    ( \ x : OA , \ x : OB , OC ) A := \ x : OB , OC ) $.

  ${
    hbl1.1 $e |- ( ph |= A : OA ) $.
    $( Deduction form of ~ ax-hbl1 .
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    hbl1 $p |- ( ph |= ( \ x : OA , \ x : OB , OC ) A := \ x : OB , OC ) $=
      ( mt om wk ol to mc wde ax-hbl1 syl ) ABHICJBCDEFKZFKLHMIQNGBCDEFOP $.
      $( [26-Feb-2016] $)
  $}

  ${
    $d x OB $.
    $( If ` x ` does not appear in ` OB ` , then any substitution to ` OB `
       yields ` OB ` again, i.e. ` \ x OB ` is a constant function. $)
    ax-17 $a |- ( A : OA |= ( \ x : OA , OB ) A := OB ) $.

    a17d.1 $e |- ( ph |= A : OA ) $.
    $( Deduction form of ~ ax-17 . $)
    a17d $p |- ( ph |= ( \ x : OA , OB ) A := OB ) $=
      ( mt om wk ol to mc wde ax-17 syl ) ABGHCIBCDEJKGLHDMFBCDENO $.
      $( [26-Feb-2016] $)
  $}

  ${
    $d x ph $.
    hbxfrf.1 $e |- ( ph |= OC := OB ) $.
    hbxfrf.2 $e |- ( ( ps , ph ) |= ( \ x : OA , OB ) A := OB ) $.
    $( Transfer a hypothesis builder to an equivalent expression.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    hbxfrf $p |- ( ( ps , ph ) |= ( \ x : OA , OC ) A := OC ) $=
      ( wa ol to mt mc om wde lded adantl bded cde1d 3detr4d ) BAJZCDEGKZLMZNOE
      CDFGKZLMZNOFIUBCUFUDUBUEUCABUEUCPADFEGHQRSTABFEPHRUA $.
      $( [26-Feb-2016] $)
  $}

  ${
    hbxfr.1 $e |- OC := OB $.
    hbxfr.2 $e |- ( ph |= ( \ x : OA , OB ) A := OB ) $.
    $( Transfer a hypothesis builder to an equivalent expression.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    hbxfr $p |- ( ph |= ( \ x : OA , OC ) A := OC ) $=
      ( ol to mt mc om wde wi wtru a1i adantr hbxfrf ancoms ex trud ) ABCEFIJKL
      MENZOPAUCAPUCPABCDEFEDNPGQAPBCDFIJKLMDNHRSTUAUB $.
      $( [26-Feb-2016] $)
  $}

  ${
    hbc.1 $e |- ( ph |= ( \ x : OA , MA ) A := MA ) $.
    hbc.2 $e |- ( ph |= ( \ x : OA , B ) A := B ) $.
    $( Hypothesis builder for combination.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    hbc $p |- ( ph |= ( \ x : OA , MA B ) A := MA B ) $=
      ( mc om ol to mt wde ax-distrc a1i bd detrd cde12d ) ABDCEIJZFKLMIJZBDCMJ
      ZFKLMIJZLZBDEJFKLMIZIJZTUAUFNABCDEFOPAUDCUEEGAUDMJUCUBAUCQHRSR $.
      $( [26-Feb-2016] $)
  $}

  ${
    $d x y $.  $d y A $.  $d y ph $.
    hbl.1 $e |- ( ph |= ( \ x : OA , OB ) A := OB ) $.
    hbl.2 $e |- ( ph |= ( \ x : OA , OC ) A := OC ) $.
    $( Hypothesis builder for lambda abstraction. $)
    hbl $p |- ( ph |= ( \ x : OA , \ y : OB , OC ) A := \ y : OB , OC ) $=
      ( ol to mt mc om wde ax-distrl a1i lde1d lded detrd ) ABCDEGJZFJKLMNZBCDF
      JKLMNZBCEFJKLMNZGJZUAUBUEOABCDEFGPQAUEDUDGJUAAUCDUDGHRADUDEGISTT $.
      $( [8-Oct-2014] $)
  $}

  $( Beta-reduce a term.
     (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  ax-beta $a |- ( x : OA |= ( \ x : OA , OB ) x := OB ) $.

  ${
    $d x ph $.
    ax-cl.1 $e |- ( ph |= A : OA ) $.
    ax-cl.2 $e |- ( ( ph , x := A ) |= OB := OC ) $.
    $( Apply a variable substitution.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    ax-cl $a |- ( ph |= ( \ x : OA , OB ) A := ( \ x : OA , OC ) A ) $.

    clf.3 $e |- ( ph |= ( \ x : OA , OC ) A := OC ) $.
    $( Evaluate a lambda expression.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    clf $p |- ( ph |= ( \ x : OA , OB ) A := OC ) $=
      ( ol to mt mc om ax-cl detrd ) ABCDFJKLMNBCEFJKLMNEABCDEFGHOIP $.
      $( [26-Feb-2016] $)
  $}

  ${
    $d x A $.  $d x OA $.  $d x OC $.
    cl.1 $e |- ( x := A |= OB := OC ) $.
    $( Evaluate a lambda expression. $)
    cl $p |- ( A : OA |= ( \ x : OA , OB ) A := OC ) $=
      ( mt om wk id tv wde adantl ax-17 clf ) AGHZBIZABCDEQJEKGHPLQCDLFMABDENO
      $.
      $( [8-Oct-2014] $)
  $}

  ${
    $d x y ph $.  $d x OA $.
    cbvf.1 $e |- ( ph |= OA : OD ) $.
    cbvf.2 $e |- ( ( ph , x : OA ) |= OB : OE ) $.
    cbvf.3 $e |- ( ( ph , x := y ) |= OB := OC ) $.
    ${
      cbvf.4 $e |- ( x : OA |= ( \ y : OA , OB ) x := OB ) $.
      cbvf.5 $e |- ( y : OA |= ( \ x : OA , OC ) y := OC ) $.
      $( Change bound variables in a lambda abstraction.
         (Contributed by Mario Carneiro, 26-Feb-2016.) $)
      cbvf $p |- ( ph |= \ x : OA , OB := \ y : OA , OC ) $=
        ( ol to mt om tv mc wde wk bd ax-kl dektrd ax-eta desymd wa simpr simpl
        syl sylan adantl clf ax-lde 3detr3d ) ABCGNZOPZQZBHRZUQSQZHNZUPBDHNAVAU
        RAURBFGNZUAVAURTAURUPVBAUPUBZABCFEGIJUCUDBFUQHGUEUJUFVCABUTDHAUSPQZBUAZ
        UGZUSBCDGAVEUHVFAGRPQVDTCDTAVEUIKUKVEAUSBDGNOPSQDTMULUMUNUO $.
        $( [26-Feb-2016] $)
    $}

    $d x OC $.  $d y OB $.
    $( Change bound variables in a lambda abstraction.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    cbv $p |- ( ph |= \ x : OA , OB := \ y : OA , OC ) $=
      ( tv ax-17 cbvf ) ABCDEFGHIJKGLBCHMHLBDGMN $.
      $( [26-Feb-2016] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Infix operator
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c [ ] $.

  $( Infix operator.
       (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  tov $a term [ A F B ] $.

  $( Infix operator. This is a simple metamath way of cleaning up the syntax
     of all these infix operators to make them a bit more readable than the
     curried representation.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  df-ov $a |- [ A F B ] := F A B $.

  ${
    oveq123d.4 $e |- ( ph |= F := S ) $.
    oveq123d.5 $e |- ( ph |= A := C ) $.
    oveq123d.6 $e |- ( ph |= B := T ) $.
    $( Equality theorem for binary operation.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    oveq123d $p |- ( ph |= [ A F B ] := [ C S T ] ) $=
      ( mt mc om tov cde12d df-ov 3detr4g ) ACBEKZLZLMGDFKZLZLMBCENKMDGFNKMACGS
      UAABDRTHIOJOBCEPDGFPQ $.
      $( [26-Feb-2016] $)
  $}

  ${
    oveq1d.4 $e |- ( ph |= A := C ) $.
    $( Equality theorem for binary operation.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    oveq1d $p |- ( ph |= [ A F B ] := [ C F B ] ) $=
      ( mt om deidd oveq123d ) ABCDEECAEGHIFACGHIJ $.
      $( [26-Feb-2016] $)

    oveq12d.5 $e |- ( ph |= B := T ) $.
    $( Equality theorem for binary operation.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    oveq12d $p |- ( ph |= [ A F B ] := [ C F T ] ) $=
      ( mt om deidd oveq123d ) ABCDEEFAEIJKGHL $.
      $( [26-Feb-2016] $)
  $}

  ${
    oveq2d.4 $e |- ( ph |= B := T ) $.
    $( Equality theorem for binary operation.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    oveq2d $p |- ( ph |= [ A F B ] := [ A F T ] ) $=
      ( mt om deidd oveq12d ) ABCBDEABGHIFJ $.
      $( [26-Feb-2016] $)
  $}

  ${
    oveqd.4 $e |- ( ph |= F := S ) $.
    $( Equality theorem for binary operation.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    oveqd $p |- ( ph |= [ A F B ] := [ A S B ] ) $=
      ( mt om deidd oveq123d ) ABCBDECFABGHIACGHIJ $.
      $( [26-Feb-2016] $)
  $}

  ${
    hbov.1 $e |- ( ph |= ( \ x : OA , F ) A := F ) $.
    hbov.2 $e |- ( ph |= ( \ x : OA , B ) A := B ) $.
    hbov.3 $e |- ( ph |= ( \ x : OA , C ) A := C ) $.
    $( Hypothesis builder for binary operation. 
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    hbov $p |- ( ph |= ( \ x : OA , [ B F C ] ) A := [ B F C ] ) $=
      ( mt mc om tov df-ov hbc hbxfr ) ABFDCEKZLZLMCDENKMGCDEOABDFSGABCFRGHIPJP
      Q $.
      $( [26-Feb-2016] $)
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y OA $.  $d x y OB $.  $d x y OD $.
    ovl.1 $e |- ( ( x := A , y := B ) |= OC := OD ) $.
    $( Evaluate a lambda expression in a binary operation.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    ovl $p |- ( ( A : OA , B : OB ) |=
      [ A ( \ x : OA , \ y : OB , OC ) B ] := OD ) $=
      ( mt om wk wa ol to mc wde simpr detrd a17d tov df-ov a1i simpl tv adantr
      dektrd ax-beta syl desymd cde2d lded df-b hbl1 hbxfr hbc hbl clf bd cde1d
      detr4d ancoms sylan ) AJKZCLZBJKZDLZMZABCDEHNZGNOZUAJKZBAVJJPZPKZFVKVMQVH
      ABVJUBUCVHVMBDACEGNZOJZPKZHNZOJZPKFVHBVLVRVHVLKVQVRKVHACVIVQGVEVGUDZVHGUE
      ZJKZVDQZMZDEVPHWCEVTVOPKZVPWCWDEWCWACLWDEQWCWAVDCVHWBRZVHWBVEVSUFUGCEGUHU
      IUJWCVTAVOWEUKSULVHACDVPGHVHACDGVSTVHAACVOGVHACVNVOKGVNUMVHACCEGVSUNUOVHA
      CVDGVSTUPUQURVHVQUSVAUTVHBDVPFHVEVGRZVHHUEJKVFQZMZACEFGVHWGVEVSUFZWHWGWBE
      FQZVHWGRWBWGWJIVBVCWHACFGWITURVHBDFHWFTURSS $.
      $( [26-Feb-2016] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Function type
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c -> $.

  $( The function type.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  tim $a term ( OA -> OB ) $.

  ${
    $d x OA $.  $d x OB $.
    $( Definition of the function type, which is just a constant function.
         (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    df-im $a |- ( OA -> OB ) := \ x : OA , OB $.

    kim2.1 $e |- ( ph |= OC : ( OA -> OB ) ) $.
    $( The type of a combination.
     (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    kim2 $p |- ( ph |= OC : \ x : OA , OB ) $=
      ( tim mt om ol wde df-im a1i kdetrd ) ADBCGHIZBCEJZFOPKABCELMN $.
      $( [26-Feb-2016] $)
  $}

  ${
    $d x ph $.  $d x OA $.  $d x OB $.  $d x OC $.  $d x OD $.
    imde1d.1 $e |- ( ph |= OA := OB ) $.
    $( Equality theorem for a constant function.
     (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    imde1d $p |- ( ph |= ( OA -> OC ) := ( OB -> OC ) ) $=
      ( vx ol tim mt om lde1d df-im 3detr4g ) ABDFGCDFGBDHIJCDHIJABCDFEKBDFLCDF
      LM $.
      $( [26-Feb-2016] $)

    imde12d.1 $e |- ( ph |= OC := OD ) $.
    $( Equality theorem for a constant function.
     (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    imde12d $p |- ( ph |= ( OA -> OC ) := ( OB -> OD ) ) $=
      ( vx tim mt om imde1d ol lded df-im 3detr4g detrd ) ABDIJKCDIJKZCEIJKZABC
      DFLACDHMCEHMRSACDEHGNCDHOCEHOPQ $.
      $( [26-Feb-2016] $)
  $}

  ${
    imde2d.1 $e |- ( ph |= OB := OC ) $.
    $( Equality theorem for a constant function.
     (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    imde2d $p |- ( ph |= ( OA -> OB ) := ( OA -> OC ) ) $=
      ( deidd imde12d ) ABBCDABFEG $.
      $( [26-Feb-2016] $)
  $}

  ${
    $d x ph $.  $d x OA $.  $d x OC $.
    kim1.1 $e |- ( ph |= OA : OD ) $.
    kim1.2 $e |- ( ( ph , x : OA ) |= OB : OC ) $.
    $( The type of a lambda abstraction.
     (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    kim1 $p |- ( ph |= \ x : OA , OB : ( OA -> OC ) ) $=
      ( ol tim mt om ax-kl wde df-im desymi a1i kdetrd ) ABCFIBDFIZBDJKLZABCDEF
      GHMSTNATSBDFOPQR $.
      $( [26-Feb-2016] $)
  $}

  ${
    $d x OA $.  $d x OB $.
    $( The type of a constant function.
     (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    imval $p |- ( A : OA |= ( OA -> OB ) A := OB ) $=
      ( vx mt om wk tim mc ol to wde df-im df-b detr4i a1i cde1d ax-17 detrd )
      AEFBGZABCHEZIFABCDJZKEZIFCTAUAUCUAFZUCFZLTUDUBUEBCDMUBNOPQABCDRS $.
      $( [26-Feb-2016] $)

    kim.1 $e |- ( ph |= OA : OD ) $.
    kim.2 $e |- ( ph |= OB : OC ) $.
    $( The type of a constant function.
     (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    kim $p |- ( ph |= ( OA -> OB ) : ( OA -> OC ) ) $=
      ( vx tim mt om ol wde df-im a1i tv wk adantr kim1 dektrd ) ABCIJKZBCHLZBD
      IJKUAUBMABCHNOABCDEHFAHPJKBQCDQGRST $.
      $( [26-Feb-2016] $)
  $}

  ${
    kcim.1 $e |- ( ph |= MA : ( OA -> OB ) ) $.
    kcim.2 $e |- ( ph |= B : OA ) $.
    $( The type of a combination.
     (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    kcim $p |- ( ph |= MA B : OB ) $=
      ( vx mc om tim mt to ol wde df-im a1i bd desymd kdetrd lde1d detrd kcd wk
      imval syl ) ABEIJBCDKLZIJZDACMZBDEUGHAEJUGJZUILJZDHNZFAUJCDHNZULUJUMOACDH
      PQACUKDHAUKCACRSZUAUBTABLJZCUKGUNTUCAUOCUDUHDOGBCDUEUFT $.
      $( [26-Feb-2016] $)
  $}

  ${
    $d x y $.  $d y ph $.  $d y A $.  $d y OB $.  $d y OC $.
    hbim.1 $e |- ( ph |= ( \ x : OA , OB ) A := OB ) $.
    hbim.2 $e |- ( ph |= ( \ x : OA , OC ) A := OC ) $.
    $( The type of a constant function.
     (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    hbim $p |- ( ph |= ( \ x : OA , ( OB -> OC ) ) A := ( OB -> OC ) ) $=
      ( vy ol tim mt om df-im hbl hbxfr ) ABCDEIJDEKLMFDEINABCDEFIGHOP $.
      $( [26-Feb-2016] $)
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                           Types and universes
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $c univ $.  $( Typecode for universes (syntax) $)
  $c u0 $.    $( Lowest universe level $)
  $c suc $.   $( Universe successor $)
  $c max $.   $( Universe join $)
  $c imax $.  $( Universe join (variant) $)
  $c u<_ $.   $( Universe ordering $)
  $c Type $.  $( Type of types $)
  $c Prop $.  $( Type of propositions $)
  $c typeof $. $( Typeof operator $)
  

  $v i j k $.  $( Universe variables $)

  $( Let variable ` i ` be a universe variable. $)
  ui $f univ i $.
  $( Let variable ` j ` be a universe variable. $)
  uj $f univ j $.
  $( Let variable ` k ` be a universe variable. $)
  uk $f univ k $.

  $( The universe zero.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  uu0 $a univ u0 $.

  $( The successor function.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  usuc $a univ suc i $.

  $( The max function.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  umax $a univ max i j $.

  $( The imax function, which is equal to ` u0 ` if ` j = u0 ` , otherwise
     ` imax i j = max i j ` .
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  uimax $a univ imax i j $.

  $( Comparison of universe levels is a deduction.  The collection of universe
     levels, modeled by the natural numbers, is a join-semilattice with a
     bottom element and a successor function.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  wule $a wff i u<_ j $.

  $( Ordering of universes is reflexive.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  ax-leid $a |- i u<_ i $.

  $( Ordering of universes is transitive.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  ax-letr $a |- ( ( i u<_ j , j u<_ k ) |= i u<_ k ) $.

  $( Zero is the bottom element of the universe order.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  ax-0le $a |- u0 u<_ i $.

  $( Comparison of universe levels is a deduction.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  ax-lesuc $a |- i u<_ suc i $.

  $( The successor function is monotonic.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  ax-sucle $a |- ( i u<_ j |= suc i u<_ suc j ) $.

  $( The maximum function is greater than the first argument.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  ax-max1 $a |- i u<_ max i j $.

  $( The maximum function is greater than the second argument.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  ax-max2 $a |- j u<_ max i j $.

  $( If both arguments are below a bound, so is the maximum.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  ax-lemax $a |- ( ( i u<_ k , j u<_ k ) |= max i j u<_ k ) $.

  $( The imax function is less than the max function.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  ax-imaxle $a |- imax i j u<_ max i j $.

  $( The imax function with zero right argument is zero.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)     
  ax-imax0 $a |- imax i u0 u<_ u0 $.

  $( The imax function with nonzero right argument is equivalent to the max
     function.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  ax-imaxsuc $a |- max i suc j u<_ imax i suc j $.

  $( The imax function of equal arguments equals the common value. This is
     provable for the natural numbers but must be assumed here since we only
     have the first order theory.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)     
  ax-imaxid $a |- i u<_ imax i i $.

  $( The type " ` Type i ` " is the set of all types at universe level ` i ` .
     The lowest one is ` Prop ` , and each Type is in the next higher one. 
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  tty $a term Type i $.

  $( The type of propositions. 
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  tpp $a term Prop $.

  $( The type of propositions. 
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  df-pp $a |- Prop := Type u0 $.

  $( The typeof operator returns the universe level in which a type resides.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  uto $a univ typeof OA $.

  $( Each type is in the next higher type. 
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  kty $a |- Type i : Type suc i $.

  $( The set of universes is a partial order, so two universe levels that are
     less than each other produce definitionally equal type universes. 
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  tyde $a |- ( ( i u<_ j , j u<_ i ) |= Type i := Type j ) $.

  $( A lambda abstraction representing a pi type is a member of the imax of the
     index type and the type of the target types.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  tyim $a |- ( ( OA : Type i , OB : ( OA -> Type j ) ) |=
               OB : Type imax i j ) $.

  ${
    tyld.1 $e |- ( ph |= OA : Type i ) $.
    tyld.2 $e |- ( ( ph , x : OA ) |= OB : Type j ) $.
    $( A lambda abstraction representing a pi type is a member of the imax of the
       index type and the type of the target types.
         (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    tyld $p |- ( ph |= \ x : OA , OB : Type imax i j ) $=
      ( tty mt om wk ol tim uimax kim1 tyim syl2anc ) ABEIJKZLBCDMZBFIJKZNJKLTE
      FOIJKLGABCUASDGHPBTEFQR $.
      $( [26-Feb-2016] $)
  $}

  ${
    tylpp.1 $e |- ( ph |= OA : Type i ) $.
    tylpp.2 $e |- ( ( ph , x : OA ) |= OB : Prop ) $.
    $( The type of a forall statement.
         (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    tylpp $p |- ( ph |= \ x : OA , OB : Prop ) $=
      ( ol uu0 uimax tty mt om tpp tv wde df-pp a1i kdetrd wule ax-imax0 ax-0le
      wk wa tyld tyde mp2an detr4i ) ABCDHEIJZKLMZNLMZABCDEIFADOLMBUCUDZCUKIKLM
      ZGUKUMPULQRSUEUJUKPAUJUMUKUIITIUITUJUMPEUAUIUBUIIUFUGQUHRS $.
      $( [26-Feb-2016] $)
  $}

  $( If ` OB ` contains an element, then it is a type, so it resides in some
     type universe, labeled by the typeof operator.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  ax-to $a |- ( OA : OB |= OB : Type typeof OB ) $.

  $( If ` OA ` is in the universe level ` i ` , then ` i ` is at least as large
     as the universe of ` OA ` .
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  ax-tole $a |- ( OA : Type i |= typeof OA u<_ i ) $.

  $( Proof irrelevance for propositions.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  ax-irrel $a |- ( OA : Prop |= ( ( OB : OA , OC : OA ) |= OB := OC ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Zero, one, two
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
  $c zero zero.rec $.
  $c one one.* one.rec $.
  $c bool tt ff cond $.

  $( The zero type, a type with no elements.
     (Contributed by Mario Carneiro, 14-Mar-2016.) $)
  t0 $a term zero $.

  $( The zero recursor.
     (Contributed by Mario Carneiro, 14-Mar-2016.) $)
  t0r $a term zero.rec $.

  $( The universe of the zero type.
     (Contributed by Mario Carneiro, 14-Mar-2016.) $)
  k0 $a |- zero : Type suc u0 $.

  $( Definition of the zero recursor, a function to any type.
     (Contributed by Mario Carneiro, 14-Mar-2016.) $)
  k0r $a |- zero.rec i : \ x : Type i , ( zero -> x ) $.

  $( The type of the zero recursor.
     (Contributed by Mario Carneiro, 14-Mar-2016.) $)
  0val $p |- ( A : Type i |= zero.rec i A : ( zero -> A ) ) $=
    ( ol uu0 uimax tty mt om tpp tv wde df-pp a1i kdetrd wule ax-imax0 ax-0le
    wk wa tyld tyde mp2an detr4i ) ABCDHEIJZKLMZNLMZABCDEIFADOLMBUCUDZCUKIKLM
    ZGUKUMPULQRSUEUJUKPAUJUMUKUIITIUITUJUMPEUAUIUBUIIUFUGQUHRS $.
    $( [26-Feb-2016] $)

  $( The one type, a type with one element.
     (Contributed by Mario Carneiro, 14-Mar-2016.) $)
  t1 $a term one $.

  $( The sole element of the one type.
     (Contributed by Mario Carneiro, 14-Mar-2016.) $)
  t1s $a term one.* $.

  $( The one recursor.
     (Contributed by Mario Carneiro, 14-Mar-2016.) $)
  t1r $a term one.rec $.

  $( Definition of the one type, as the set of all functions from zero to
     itself.
     (Contributed by Mario Carneiro, 14-Mar-2016.) $)
  df-1 $a |- one := ( zero -> zero ) $.

  $( Definition of the unique element of the one type, the identity function on
     zero.
     (Contributed by Mario Carneiro, 14-Mar-2016.) $)
  df-1s $a |- one.* := \ x : zero , x $.

  $( Definition of the one recursor.
     (Contributed by Mario Carneiro, 14-Mar-2016.) $)
  df-1r $a |- one.rec i := \ x : Type i , \ y : x , \ z : one , y $.

  $( The star is a member of its type.
     (Contributed by Mario Carneiro, 14-Mar-2016.) $)
  k1s $p |- one.* : one $=
    ( ol uu0 uimax tty mt om tpp tv wde df-pp a1i kdetrd wule ax-imax0 ax-0le
    wk wa tyld tyde mp2an detr4i ) ABCDHEIJZKLMZNLMZABCDEIFADOLMBUCUDZCUKIKLM
    ZGUKUMPULQRSUEUJUKPAUJUMUKUIITIUITUJUMPEUAUIUBUIIUFUGQUHRS $.
    $( [14-Mar-2016] $)

  $( Type of the one recursor.
     (Contributed by Mario Carneiro, 14-Mar-2016.) $)
  k1r $p |- one.rec i : \ x : Type i , ( x -> ( one -> x ) ) $=
    ? $.

  ${
    de1s.1 $e |- ( ph |= OA : Type i ) $.
    de1s.2 $e |- ( ph |= A : OA ) $.
    $( The equality rule for the star.
       (Contributed by Mario Carneiro, 14-Mar-2016.) $)
    de1s $p |- ( ph |= one.rec i A one.* := A ) $=
      ( ol uu0 uimax tty mt om tpp tv wde df-pp a1i kdetrd wule ax-imax0 ax-0le
      wk wa tyld tyde mp2an detr4i ) ABCDHEIJZKLMZNLMZABCDEIFADOLMBUCUDZCUKIKLM
      ZGUKUMPULQRSUEUJUKPAUJUMUKUIITIUITUJUMPEUAUIUBUIIUFUGQUHRS $.
      $( [14-Mar-2016] $)
  $}

  $( The boolean type, a type with two elements.
     (Contributed by Mario Carneiro, 14-Mar-2016.) $)
  t2 $a term bool $.

  $( The first element of the boolean type, "true".
     (Contributed by Mario Carneiro, 14-Mar-2016.) $)
  ttt $a term tt $.

  $( The second element of the boolean type, "false".
     (Contributed by Mario Carneiro, 14-Mar-2016.) $)
  tff $a term ff $.

  $( The universe of the zero type.
     (Contributed by Mario Carneiro, 14-Mar-2016.) $)
  k2 $a |- bool : Type suc u0 $.

  $( True is a boolean value.
     (Contributed by Mario Carneiro, 14-Mar-2016.) $)
  ktt $a |- tt : bool $.

  $( False is a boolean value.
     (Contributed by Mario Carneiro, 14-Mar-2016.) $)
  kff $a |- ff : bool $.

  $( The conditional (bool recursor).
     (Contributed by Mario Carneiro, 14-Mar-2016.) $)
  kcl $a |- cond i : \ x : Type i , ( bool -> ( x -> ( x -> x ) ) ) $.

  ${
    dett.1 $e |- ( ph |= OA : Type i ) $.
    dett.2 $e |- ( ph |= A : OA ) $.
    dett.3 $e |- ( ph |= B : OA ) $.    
    $( The equality rule for the conditional, true case.
       (Contributed by Mario Carneiro, 14-Mar-2016.) $)
    dett $a |- ( ph |= cond i tt A B := A ) $.
      $( [26-Feb-2016] $)

    $( The equality rule for the conditional, false case.
       (Contributed by Mario Carneiro, 14-Mar-2016.) $)
    deff $a |- ( ph |= cond i ff A B := B ) $.
      $( [26-Feb-2016] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Sigma type
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c sigma $.
  $c sigma1 $.
  $c sigma2 $.
  $c pair $.
  $c 1st $.
  $c 2nd $.

  $( The sigma type, the equivalent of an indexed disjoint union in ZFC.
     (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  tsig $a term sigma i j $.

  $( The first component function for a sigma type.
     (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  t1st $a term 1st i j $.

  $( The second component function for a sigma type.
     (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  t2nd $a term 2nd i j $.

  $( The pair function for a sigma type.
     (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  tpair $a term pair i j $.

  $( Type of the sigma type.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  ksig $a |- sigma i j : \ x : Type i , \ y : ( x -> Type j ) ,
             Type max suc u0 max i j ) $.

  $( Type of the first component function.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  k1st $a |- 1st i j : \ x : Type i , \ y : ( x -> Type j ) ,
              ( sigma i j x y -> x ) $.

  $( Type of the second component function.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  k2nd $a |- 2nd i j : \ x : Type i , \ y : ( x -> Type j ) ,
              \ p : sigma i j x y , y ( sigma1 i j x y p ) $.

  $( Type of the pair function.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  kpair $a |- pair i j : \ x : Type i , \ y : ( x -> Type j ) ,
              \ p : x , ( y p -> sigma i j x y ) $.

  ${
    kpair1.1 $e |- ( ph |= A : Type i ) $.
    kpair1.2 $e |- ( ph |= B : ( A -> Type j ) ) $.
    kpair1.3 $e |- ( ph |= C : A ) $.
    kpair1.4 $e |- ( ph |= D : B C ) $.
    $( Type of the pair function.
         (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    kpaird $p |- ( ph |= pair i j A B C D : sigma i j A B ) $=
      ? $.

    $( Equality theorem for the sigma type.
         (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    desig1 $a |- ( ph |= sigma1 i j A B pair i j A B C D := C ) $.

    $( Equality theorem for the sigma type.
         (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    desig2 $a |- ( ph |= sigma2 i j A B pair i j A B C D := D ) $.
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                           Inductive definitions
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$( $t

/* The '$ t' (no space between '$' and 't') token indicates the beginning
    of the typesetting definition section, embedded in a Metamath
    comment.  There may only be one per source file, and the typesetting
    section ends with the end of the Metamath comment.  The typesetting
    section uses C-style comment delimiters.  Todo:  Allow multiple
    typesetting comments */

/* These are the LaTeX and HTML definitions in the order the tokens are
    introduced in $c or $v statements.  See HELP TEX or HELP HTML in the
    Metamath program. */

/******* Web page format settings *******/

/* Page title, home page link */
htmltitle "Higher-Order Logic Explorer";
htmlhome '<A HREF="mmhol.html"><FONT SIZE=-2 FACE=sans-serif>' +
    '<IMG SRC="hol.gif" BORDER=0 ALT=' +
    '"Home" HEIGHT=32 WIDTH=32 ALIGN=MIDDLE>' +
    'Home</FONT></A>';
/* Optional file where bibliographic references are kept */
/* If specified, e.g. "mmset.html", Metamath will hyperlink all strings of the
   form "[rrr]" (where "rrr" has no whitespace) to "mmset.html#rrr" */
/* A warning will be given if the file "mmset.html" with the bibliographical
   references is not present.  It is read in order to check correctness of
   the references. */
htmlbibliography "mmhol.html";

/* Variable color key at the bottom of each proof table */
htmlvarcolor '<FONT COLOR="#0000FF">type</FONT> '
    + '<FONT COLOR="#FF0000">var</FONT> '
    + '<FONT COLOR="#CC33CC">term</FONT>';

/* GIF and Unicode HTML directories - these are used for the GIF version to
   crosslink to the Unicode version and vice-versa */
htmldir "../holgif/";
althtmldir "../holuni/";


/******* Symbol definitions *******/

htmldef "wff" as '<FONT COLOR="#808080">wff </FONT>';
  althtmldef "wff" as '<FONT COLOR="#808080">wff </FONT>';
  latexdef "wff" as "{\rm wff}";
htmldef "var" as '<FONT COLOR="#808080">var </FONT>';
  althtmldef "var" as '<FONT COLOR="#808080">var </FONT>';
  latexdef "var" as "{\rm var}";
htmldef "type" as '<FONT COLOR="#808080">type </FONT>';
  althtmldef "type" as '<FONT COLOR="#808080">type </FONT>';
  latexdef "type" as "{\rm type}";
htmldef "term" as '<FONT COLOR="#808080">term </FONT>';
  althtmldef "term" as '<FONT COLOR="#808080">term </FONT>';
  latexdef "term" as "{\rm term}";
htmldef "|-" as
    "<IMG SRC='_vdash.gif' WIDTH=10 HEIGHT=19 ALT='|-' ALIGN=TOP> ";
  althtmldef "|-" as
    '<FONT COLOR="#808080" FACE=sans-serif>&#8866; </FONT>'; /* &vdash; */
    /* Without sans-serif, way too big in FF3 */
  latexdef "|-" as "\vdash";
htmldef ":" as "<IMG SRC='colon.gif' WIDTH=4 HEIGHT=19 ALT=':' ALIGN=TOP>";
  althtmldef ":" as ':';
  latexdef ":" as ":";
htmldef "." as " ";
  althtmldef "." as ' ';
  latexdef "." as "\,";
htmldef "|=" as
    " <IMG SRC='models.gif' WIDTH=12 HEIGHT=19 ALT='|=' ALIGN=TOP> ";
  althtmldef "|=" as "&#8871;"; latexdef "|=" as "\models";
htmldef "bool" as
    "<IMG SRC='hexstar.gif' WIDTH=11 HEIGHT=19 ALT='*' ALIGN=TOP>";
  althtmldef "bool" as '&lowast;';
  latexdef "bool" as "\ast";
htmldef "ind" as
    "<IMG SRC='iota.gif' WIDTH=6 HEIGHT=19 ALT='iota' ALIGN=TOP>";
  althtmldef "ind" as '<FONT SIZE="+1">&iota;</FONT>';
  latexdef "ind" as "\iota";
htmldef "->" as
    " <IMG SRC='to.gif' WIDTH=15 HEIGHT=19 ALT='-&gt;' ALIGN=TOP> ";
  althtmldef "->" as ' &rarr; ';
  latexdef "->" as "\rightarrow";
htmldef "(" as "<IMG SRC='lp.gif' WIDTH=5 HEIGHT=19 ALT='(' ALIGN=TOP>";
  althtmldef "(" as "(";
  latexdef "(" as "(";
htmldef ")" as "<IMG SRC='rp.gif' WIDTH=5 HEIGHT=19 ALT=')' ALIGN=TOP>";
  althtmldef ")" as ")";
  latexdef ")" as ")";
htmldef "," as "<IMG SRC='comma.gif' WIDTH=4 HEIGHT=19 ALT=',' ALIGN=TOP> ";
  althtmldef "," as ', ';
  latexdef "," as ",";
htmldef "\" as "<IMG SRC='lambda.gif' WIDTH=9 HEIGHT=19 ALT='\' ALIGN=TOP>";
  althtmldef "\" as '<I>&lambda;</I>';
  latexdef "\" as "\lambda";
htmldef "=" as " <IMG SRC='eq.gif' WIDTH=12 HEIGHT=19 ALT='=' ALIGN=TOP> ";
  althtmldef "=" as ' = '; /* &equals; */
  latexdef "=" as "=";
htmldef "T." as "<IMG SRC='top.gif' WIDTH=11 HEIGHT=19 ALT='T.' ALIGN=TOP>";
  althtmldef "T." as '&#x22A4;';
  latexdef "T." as "\top";
htmldef "[" as "<IMG SRC='lbrack.gif' WIDTH=5 HEIGHT=19 ALT='[' ALIGN=TOP>";
  althtmldef "[" as '['; /* &lsqb; */
  latexdef "[" as "[";
htmldef "]" as "<IMG SRC='rbrack.gif' WIDTH=5 HEIGHT=19 ALT=']' ALIGN=TOP>";
  althtmldef "]" as ']'; /* &rsqb; */
  latexdef "]" as "]";
htmldef "al" as
    "<IMG SRC='_alpha.gif' WIDTH=12 HEIGHT=19 ALT='al' ALIGN=TOP>";
  althtmldef "al" as '<FONT COLOR="#0000FF"><I>&alpha;</I></FONT>';
  latexdef "al" as "\alpha";
htmldef "be" as
    "<IMG SRC='_beta.gif' WIDTH=11 HEIGHT=19 ALT='be' ALIGN=TOP>";
  althtmldef "be" as '<FONT COLOR="#0000FF"><I>&beta;</I></FONT>';
  latexdef "be" as "\beta";
htmldef "ga" as
    "<IMG SRC='_gamma.gif' WIDTH=11 HEIGHT=19 ALT='ga' ALIGN=TOP>";
  althtmldef "ga" as '<FONT COLOR="#0000FF"><I>&gamma;</I></FONT>';
  latexdef "ga" as "\gamma";
htmldef "de" as
    "<IMG SRC='_delta.gif' WIDTH=9 HEIGHT=19 ALT='de' ALIGN=TOP>";
  althtmldef "de" as '<FONT COLOR="#0000FF"><I>&delta;</I></FONT>';
  latexdef "de" as "\delta";
htmldef "x" as "<IMG SRC='_x.gif' WIDTH=10 HEIGHT=19 ALT='x' ALIGN=TOP>";
  althtmldef "x" as '<I><FONT COLOR="#FF0000">x</FONT></I>';
  latexdef "x" as "x";
htmldef "y" as "<IMG SRC='_y.gif' WIDTH=9 HEIGHT=19 ALT='y' ALIGN=TOP>";
  althtmldef "y" as '<I><FONT COLOR="#FF0000">y</FONT></I>';
  latexdef "y" as "y";
htmldef "z" as "<IMG SRC='_z.gif' WIDTH=9 HEIGHT=19 ALT='z' ALIGN=TOP>";
  althtmldef "z" as '<I><FONT COLOR="#FF0000">z</FONT></I>';
  latexdef "z" as "z";
htmldef "f" as "<IMG SRC='_f.gif' WIDTH=9 HEIGHT=19 ALT='f' ALIGN=TOP>";
  althtmldef "f" as '<I><FONT COLOR="#FF0000">f</FONT></I>';
  latexdef "f" as "f";
htmldef "g" as "<IMG SRC='_g.gif' WIDTH=9 HEIGHT=19 ALT='g' ALIGN=TOP>";
  althtmldef "g" as '<I><FONT COLOR="#FF0000">g</FONT></I>';
  latexdef "g" as "g";
htmldef "p" as "<IMG SRC='_p.gif' WIDTH=10 HEIGHT=19 ALT='p' ALIGN=TOP>";
  althtmldef "p" as '<I><FONT COLOR="#FF0000">p</FONT></I>';
  latexdef "p" as "p";
htmldef "q" as "<IMG SRC='_q.gif' WIDTH=8 HEIGHT=19 ALT='q' ALIGN=TOP>";
  althtmldef "q" as '<I><FONT COLOR="#FF0000">q</FONT></I>';
  latexdef "q" as "q";
htmldef "A" as "<IMG SRC='_ca.gif' WIDTH=11 HEIGHT=19 ALT='A' ALIGN=TOP>";
  althtmldef "A" as '<I><FONT COLOR="#CC33CC">A</FONT></I>';
  latexdef "A" as "A";
htmldef "B" as "<IMG SRC='_cb.gif' WIDTH=12 HEIGHT=19 ALT='B' ALIGN=TOP>";
  althtmldef "B" as '<I><FONT COLOR="#CC33CC">B</FONT></I>';
  latexdef "B" as "B";
htmldef "C" as "<IMG SRC='_cc.gif' WIDTH=12 HEIGHT=19 ALT='C' ALIGN=TOP>";
  althtmldef "C" as '<I><FONT COLOR="#CC33CC">C</FONT></I>';
  latexdef "C" as "C";
htmldef "F" as "<IMG SRC='_cf.gif' WIDTH=13 HEIGHT=19 ALT='F' ALIGN=TOP>";
  althtmldef "F" as '<I><FONT COLOR="#CC33CC">F</FONT></I>';
  latexdef "F" as "F";
htmldef "R" as "<IMG SRC='_cr.gif' WIDTH=12 HEIGHT=19 ALT='R' ALIGN=TOP>";
  althtmldef "R" as '<I><FONT COLOR="#CC33CC">R</FONT></I>';
  latexdef "R" as "R";
htmldef "S" as "<IMG SRC='_cs.gif' WIDTH=11 HEIGHT=19 ALT='S' ALIGN=TOP>";
  althtmldef "S" as '<I><FONT COLOR="#CC33CC">S</FONT></I>';
  latexdef "S" as "S";
htmldef "T" as "<IMG SRC='_ct.gif' WIDTH=12 HEIGHT=19 ALT='T' ALIGN=TOP>";
  althtmldef "T" as '<I><FONT COLOR="#CC33CC">T</FONT></I>';
  latexdef "T" as "T";
htmldef "F." as "<IMG SRC='perp.gif' WIDTH=11 HEIGHT=19 ALT='F.' ALIGN=TOP>";
  althtmldef "F." as '&perp;';
  latexdef "F." as "\bot";
htmldef "/\" as
    " <IMG SRC='wedge.gif' WIDTH=11 HEIGHT=19 ALT='/\' ALIGN=TOP> ";
  althtmldef "/\" as ' <FONT FACE=sans-serif>&and;</FONT> ';
    /* althtmldef "/\" as ' <FONT FACE=sans-serif>&#8896;</FONT> '; */
    /* was &and; which is circle in Mozilla on WinXP Pro (but not Home) */
    /* Changed back 6-Mar-2012 NM */
  latexdef "/\" as "\wedge";
htmldef "~" as "<IMG SRC='lnot.gif' WIDTH=10 HEIGHT=19 ALT='~' ALIGN=TOP> "; 
  althtmldef "~" as '&not; ';
  latexdef "~" as "\lnot";
htmldef "==>" as
    " <IMG SRC='bigto.gif' WIDTH=15 HEIGHT=19 ALT='==&gt;' ALIGN=TOP> ";
  althtmldef "==>" as ' &rArr; ';
  latexdef "==>" as "\Rightarrow";
htmldef "!" as "<IMG SRC='forall.gif' WIDTH=10 HEIGHT=19 ALT='A.' ALIGN=TOP>";
  althtmldef "!" as '<FONT FACE=sans-serif>&forall;</FONT>'; /* &#8704; */
  latexdef "!" as "\forall";
htmldef "?" as "<IMG SRC='exists.gif' WIDTH=9 HEIGHT=19 ALT='E.' ALIGN=TOP>";
  althtmldef "?" as '<FONT FACE=sans-serif>&exist;</FONT>'; /* &#8707; */
    /* Without sans-serif, bad in Opera and way too big in FF3 */
  latexdef "?" as "\exists";
htmldef "\/" as " <IMG SRC='vee.gif' WIDTH=11 HEIGHT=19 ALT='\/' ALIGN=TOP> ";
  althtmldef "\/" as ' <FONT FACE=sans-serif> &or;</FONT> ' ;
    /* althtmldef "\/" as ' <FONT FACE=sans-serif>&#8897;</FONT> ' ; */
    /* was &or; - changed to match font of &and; replacement */
    /* Changed back 6-Mar-2012 NM */
  latexdef "\/" as "\vee";
htmldef "?!" as "<IMG SRC='_e1.gif' WIDTH=12 HEIGHT=19 ALT='E!' ALIGN=TOP>";
  althtmldef "?!" as '<FONT FACE=sans-serif>&exist;!</FONT>';
  latexdef "?!" as "\exists{!}";
htmldef "typedef" as "typedef ";
  althtmldef "typedef" as 'typedef ';
  latexdef "typedef" as "\mbox{typedef }";
htmldef "1-1" as "1-1 ";
  althtmldef "1-1" as '1-1 ';
  latexdef "1-1" as "\mbox{1-1 }";
htmldef "onto" as "onto ";
  althtmldef "onto" as 'onto ';
  latexdef "onto" as "\mbox{onto }";
htmldef "@" as
    "<IMG SRC='varepsilon.gif' WIDTH=8 HEIGHT=19 ALT='@' ALIGN=TOP>";
  althtmldef "@" as '&epsilon;';
  latexdef "@" as "\varepsilon";

/* End of typesetting definition section */
$)

$( 456789012345 (79-character line to adjust text window width) 567890123456 $)


