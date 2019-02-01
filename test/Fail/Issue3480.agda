-- Andreas, 2018-12-30, issue #3480

-- Parse error should be reported close to the incomplete "module _"
-- rather than at the end of the file, which is miles away.

module _

{- A long comment:


Per Martin-L"of
ON THE MEANINGS OF THE LOGICAL
CONSTANTS AND THE JUSTIFICATIONS
OF THE LOGICAL LAWS

Preface
The following three lectures were given in the form of a short course
at the meeting Teoria della Dimostrazione e Filosofia della Logica,
organized in Siena, 6-9 April 1983, by the Scuola di Specializzazione in
Logica Matematica of the Universit`a degli Studi di Siena. I am very
grateful to Giovanni Sambin and Aldo Ursini of that school, not only
for recording the lectures on tape, but, above all, for transcribing the
tapes produced by the recorder: no machine could have done that work.
This written version of the lectures is based on their transcription. The
changes that I have been forced to make have mostly been of a stylistic
nature, except at one point. In the second lecture, as I actually gave
it, the order of conceptual priority between the notions of proof and
immediate inference was wrong. Since I discovered my mistake later
the same month as the meeting was held, I thought it better to let
the written text diverge from the oral presentation rather than possibly
confusing others by letting the mistake remain. The oral origin of
these lectures is the source of the many redundancies of the written
text. It is also my sole excuse for the lack of detailed references.

First lecture
When I was asked to give these lectures about a year ago, I suggested
the title On the Meanings of the Logical Constants and the
Justifications of the Logical Laws. So that is what I shall talk about,
eventually, but, first of all, I shall have to say something about, on
the one hand, the things that the logical operations operate on, which
we normally call propositions and propositional functions, and, on the

Nordic Journal of Philosophical Logic, Vol. 1, No. 1, pp. 11-60.

cfl 1996 Scandinavian University Press.

12 per martin-l"of
other hand, the things that the logical laws, by which I mean the rules
of inference, operate on, which we normally call assertions. We must
remember that, even if a logical inference, for instance, a conjunction
introduction, is written

A B

A & B

which is the way in which we would normally write it, it does not take
us from the propositions A and B to the proposition A & B. Rather, it
takes us from the affirmation of A and the affirmation of B to the
affirmation of A & B, which we may make explicit, using Frege's notation,
by writing it `

A ` B

` A & B

instead. It is always made explicit in this way by Frege in his writings,
and in Principia, for instance. Thus we have two kinds of entities here:
we have the entities that the logical operations operate on, which we
call propositions, and we have those that we prove and that appear
as premises and conclusion of a logical inference, which we call assertions. It turns out that, in order to clarify the meanings of the logical
constants and justify the logical laws, a considerable portion of the
philosophical work lies already in clarifying the notion of proposition
and the notion of assertion. Accordingly, a large part of my lectures
will be taken up by a philosophical analysis of these two notions.

Let us first look at the term proposition. It has its origin in the Gr.
pri`tasij, used by Aristotle in the Prior Analytics, the third part of the
Organon. It was translated, apparently by Cicero, into Lat. propositio,
which has its modern counterparts in It. proposizione, Eng. proposition and Ger. Satz. In the old, traditional use of the word proposition,
propositions are the things that we prove. We talk about proposition
and proof, of course, in mathematics: we put up a proposition and let
it be followed by its proof. In particular, the premises and conclusion
of an inference were propositions in this old terminology. It was the
standard use of the word up to the last century. And it is this use
which is retained in mathematics, where a theorem is sometimes called
a proposition, sometimes a theorem. Thus we have two words for the
things that we prove, proposition and theorem. The word proposition,
Gr. pri`tasij, comes from Aristotle and has dominated the logical tradition, whereas the word theorem, Gr. qey"rhma, is in Euclid, I believe,
and has dominated the mathematical tradition.

With Kant, something important happened, namely, that the
term judgement, Ger. Urteil, came to be used instead of proposition.

on the meanings of the logical constants 13
Perhaps one reason is that proposition, or a word with that stem, at
least, simply does not exist in German: the corresponding German
word would be Lehrsatz, or simply Satz. Be that as it may, what happened with Kant and the ensuing German philosophical tradition was
that the word judgement came to replace the word proposition. Thus,
in that tradition, a proof, Ger. Beweis, is always a proof of a judgement. In particular, the premises and conclusion of a logical inference
are always called judgements. And it was the judgements, or the categorical judgements, rather, which were divided into affirmations and
denials, whereas earlier it was the propositions which were so divided.

The term judgement also has a long history. It is the Gr. krDHsij,
translated into Lat. judicium, It. giudizio, Eng. judgement, and Ger.
Urteil. Now, since it has as long a history as the word proposition,
these two were also previously used in parallel. The traditional way of
relating the notions of judgement and proposition was by saying that a
proposition is the verbal expression of a judgement. This is, as far as I
know, how the notions of proposition and judgement were related during the scholastic period, and it is something which is repeated in the
Port Royal Logic, for instance. You still find it repeated by Brentano
in this century. Now, this means that, when, in German philosophy
beginning with Kant, what was previously called a proposition came
to be called a judgement, the term judgement acquired a double meaning. It came to be used, on the one hand, for the act of judging, just
as before, and, on the other hand, it came to be used instead of the old
proposition. Of course, when you say that a proposition is the verbal
expression of a judgement, you mean by judgement the act of judging,
the mental act of judging in scholastic terms, and the proposition is the
verbal expression by means of which you make the mental judgement
public, so to say. That is, I think, how one thought about it. Thus,
with Kant, the term judgement became ambiguous between the act of
judging and that which is judged, or the judgement made, if you prefer.
German has here the excellent expression gef"alltes Urteil, which has no
good counterpart in English.

judgement
z ""-- -

the act of judging that which is judged
old tradition judgement proposition
Kant Urteil(sakt) (gef"alltes) Urteil

This ambiguity is not harmful, and sometimes it is even convenient,
because, after all, it is a kind of ambiguity that the word judgement

14 per martin-l"of
shares with other nouns of action. If you take the word proposition,
for instance, it is just as ambiguous between the act of propounding
and that which is propounded. Or, if you take the word affirmation, it
is ambiguous between the act of affirming and that which is affirmed,
and so on.

It should be clear, from what I said in the beginning, that there is
a difference between what we now call a proposition and a proposition
in the old sense. In order to trace the emergence of the modern notion
of proposition, I first have to consider the division of propositions in
the old sense into affirmations and denials. Thus the propositions, or
the categorical propositions, rather, were divided into affirmations and
denials.

(categorical) proposition

z ""-- -

affirmation denial

And not only were the categorical propositions so divided: the very
definition of a categorical proposition was that a categorical proposition
is an affirmation or a denial. Correlatively, to judge was traditionally,
by which I mean before Kant, defined as to combine or separate ideas
in the mind, that is, to affirm or deny. Those were the traditional
definitions of the notions of proposition and judgement.

The notions of affirmation and denial have fortunately remained
stable, like the notion of proof, and are therefore easy to use without
ambiguity. Both derive from Aristotle. Affirmation is Gr. katL'fasij,
Lat. affirmatio, It. affermazione, and Ger. Bejahung, whereas denial
is Gr. C'pi`fasij, Lat. negatio, It. negazione, and Ger. Verneinung. In
Aristotelian logic, an affirmation was defined as a proposition in which
something, called the predicate, is affirmed of something else, called
the subject, and a denial was defined as a proposition in which the
predicate is denied of the subject. Now, this is something that we have
certainly abandoned in modern logic. Neither do we take categorical
judgements to have subject-predicate form, nor do we treat affirmation
and denial symmetrically. It seems to have been Bolzano who took the
crucial step of replacing the Aristotelian forms of judgement by the
single form

A is, A is true, or A holds.
In this, he was followed by Brentano, who also introduced the opposite
form

A is not, or A is false,

on the meanings of the logical constants 15
and Frege. And, through Frege's influence, the whole of modern logic
has come to be based on the single form of judgement, or assertion, A
is true.

Once this step was taken, the question arose, What sort of thing
is it that is affirmed in an affirmation and denied in a denial? that is,
What sort of thing is the A here? The isolation of this concept belongs
to the, if I may so call it, objectivistically oriented branch of German
philosophy in the last century. By that, I mean the tradition which you
may delimit by mentioning the names of, say, Bolzano, Lotze, Frege,
Brentano, and the Brentano disciples Stumpf, Meinong, and Husserl,
although, with Husserl, I think one should say that the split between
the objectivistic and the Kantian branches of German philosophy is
finally overcome. The isolation of this concept was a step which was
entirely necessary for the development of modern logic. Modern logic
simply would not work unless we had this concept, because it is on the
things that fall under it that the logical operations operate.

This new concept, which simply did not exist before the last century, was variously called. And, since it was something that one had not
met before, one had difficulties with what one should call it. Among
the terms that were used, I think the least committing one is Ger.
Urteilsinhalt, content of a judgement, by which I mean that which is
affirmed in an affirmation and denied in a denial. Bolzano, who was
the first to introduce this concept, called it proposition in itself, Ger.
Satz an sich. Frege also grappled with this terminological problem.
In Begriffsschrift, he called it judgeable content, Ger. beurteilbarer Inhalt. Later on, corresponding to his threefold division into expression, sense, and reference, in the case of this kind of entity, what was
the expression, he called sentence, Ger. Satz, what was the sense, he
called thought, Ger. Gedanke, and what was the reference, he called
truth value, Ger. Wahrheitswert. So the question arises, What should
I choose here? Should I choose sentence, thought, or truth value? The
closest possible correspondence is achieved, I think, if I choose Gedanke,
that is, thought, for late Frege. This is confirmed by the fact that, in
his very late logical investigations, he called the logical operations the
Gedankengef"uge. Thus judgeable content is early Frege and thought
is late Frege. We also have the term state of affairs, Ger. Sachverhalt,
which was introduced by Stumpf and used by Wittgenstein in the Tractatus. And, finally, we have the term objective, Ger. Objektiv, which
was the term used by Meinong. Maybe there were other terms as well
in circulation, but these are the ones that come immediately to my
mind.

Now, Russell used the term proposition for this new notion, which

16 per martin-l"of
has become the standard term in Anglo-Saxon philosophy and in modern logic. And, since he decided to use the word proposition in this
new sense, he had to use another word for the things that we prove and
that figure as premises and conclusion of a logical inference. His choice
was to translate Frege's Urteil, not by judgement, as one would expect,
but by assertion. And why, one may ask, did he choose the word assertion rather than translate Urteil literally by judgement? I think it
was to avoid any association with Kantian philosophy, because Urteil
was after all the central notion of logic as it was done in the Kantian
tradition. For instance, in his transcendental logic, which forms part
of the Kritik der reinen Vernunft, Kant arrives at his categories by
analysing the various forms that a judgement may have. That was his
clue to the discovery of all pure concepts of reason, as he called it.
Thus, in Russell's hands, Frege's Urteil came to be called assertion,
and the combination of Frege's Urteilsstrich, judgement stroke, and
Inhaltsstrich, content stroke, came to be called the assertion sign.

Observe now where we have arrived through this development,
namely, at a notion of proposition which is entirely different, or different, at least, from the old one, that is, from the Gr. pri`tasij and
the Lat. propositio. To repeat, the things that we prove, in particular, the premises and conclusion of a logical inference, are no longer
propositions in Russell's terminology, but assertions. Conversely, the
things that we combine by means of the logical operations, the connectives and the quantifiers, are not propositions in the old sense, that
is, what Russell calls assertions, but what he calls propositions. And,
as I said in the very beginning, the rule of conjunction introduction,
for instance, really allows us to affirm A & B, having affirmed A and
having affirmed B, `

A ` B

` A & B

It is another matter, of course, that we may adopt conventions that
allow us to suppress the assertion sign, if it becomes too tedious to
write it out. Conceptually, it would nevertheless be there, whether I
write it as above or A true B true

A & B true
as I think that I shall do in the following.

So far, I have made no attempt at defining the notions of judgement, or assertion, and proposition. I have merely wanted to give a
preliminary hint at the difference between the two by showing how the
terminology has evolved.

on the meanings of the logical constants 17
To motivate my next step, consider any of the usual inference rules
of the propositional or predicate calculus. Let me take the rule of
disjunction introduction this time, for some change,

A
A . B

or, writing out the affirmation,

A true
A . B true

Now, what do the variables A and B range over in a rule like this?
That is, what are you allowed to insert into the places indicated by
these variables? The standard answer to this question, by someone
who has received the now current logical education, would be to say
that A and B range over arbitrary formulas of the language that you are
considering. Thus, if the language is first order arithmetic, say, then
A and B should be arithmetical formulas. When you start thinking
about this answer, you will see that there is something strange about
it, namely, its language dependence. Because it is clearly irrelevant for
the validity of the rule whether A and B are arithmetical formulas, corresponding to the language of first order arithmetic, or whether they
contain, say, predicates defined by transfinite, or generalized, induction. The unary predicate expressing that a natural number encodes
an ordinal of the constructive second number class, for instance, is certainly not expressible in first order arithmetic, and there is no reason
at all why A and B should not be allowed to contain that predicate.
Or, surely, for the validity of the rule, A and B might just as well
be set theoretical formulas, supposing that we have given such a clear
sense to them that we clearly recognize that they express propositions.
Thus what is important for the validity of the rule is merely that A and
B are propositions, that is, that the expressions which we insert into
the places indicated by the variables A and B express propositions. It
seems, then, that the deficiency of the first answer, by which I mean
the answer that A and B should range over formulas, is eliminated
by saying that the variables A and B should range over propositions
instead of formulas. And this is entirely natural, because, after all, the
notion of formula, as given by the usual inductive definition, is nothing
but the formalistic substitute for the notion of proposition: when you
divest a proposition in some language of all sense, what remains is the
mere formula. But then, supposing we agree that the natural way out
of the first difficulty is to say that A and B should range over arbitrary

18 per martin-l"of
propositions, another difficulty arises, because, whereas the notion of
formula is a syntactic notion, a formula being defined as an expression
that can be formed by means of certain formation rules, the notion
of proposition is a semantic notion, which means that the rule is no
longer completely formal in the strict sense of formal logic. That a rule
of inference is completely formal means precisely that there must be
no semantic conditions involved in the rule: it may only put conditions
on the forms of the premises and conclusion. The only way out of this
second difficulty seems to be to say that, really, the rule has not one
but three premises, so that, if we were to write them all out, it would
read A prop B prop A true

A . B true
that is, from A and B being propositions and from the truth of A, we
are allowed to conclude the truth of A . B. Here I am using

A prop
as an abbreviated way of saying that

A is a proposition.
Now the complete formality of the rule has been restored. Indeed, for
the variables A and B, as they occur in this rule, we may substitute
anything we want, and, by anything, I mean any expressions. Or, to
be more precise, if we categorize the expressions, as Frege did, into
complete, or saturated, expressions and incomplete, unsaturated, or
functional, expressions, then we should say that we may substitute for
A and B any complete expressions we want, because propositions are
always expressed by complete expressions, not by functional expressions. Thus A and B now range over arbitrary complete expressions.
Of course, there would be needed here an analysis of what is understood by an expression, but that is something which I shall not go into
in these lectures, in the belief that it is a comparatively trivial matter,
as compared with explaining the notions of proposition and judgement.
An expression in the most general sense of the word is nothing but a
form, that is, something that we can passively recognize as the same in
its manifold occurrences and actively reproduce in many copies. But
I think that I shall have to rely here upon an agreement that we have
such a general notion of expression, which is formal in character, so
that the rule can now count as a formal rule.

Now, if we stick to our previous decision to call what we prove, in
particular, the premises and conclusion of a logical inference, by the

on the meanings of the logical constants 19
word judgement, or assertion, the outcome of the preceding considerations is that we are faced with a new form of judgement. After all, A
prop and B prop have now become premises of the rule of disjunction
introduction. Hence, if premises are always judgements,

A is a proposition
must count as a form of judgement. This immediately implies that the
traditional definition of the act of judging as an affirming or denying
and of the judgement, that is, the proposition in the terminology then
used, as an affirmation or denial has to be rejected, because A prop is
certainly neither an affirmation nor a denial. Or, rather, we are faced
with the choice of either keeping the old definition of judgement as
an affirmation or a denial, in which case we would have to invent a
new term for the things that we prove and that figure as premises and
conclusion of a logical inference, or else abandoning the old definition
of judgement, widening it so as to make room for A is a proposition
as a new form of judgement. I have chosen the latter alternative, well
aware that, in so doing, I am using the word judgement in a new way.

Having rejected the traditional definition of a judgement as an affirmation or a denial, by what should we replace it? How should we
now delimit the notion of judgement, so that A is a proposition, A
is true, and A is false all become judgements? And there are other
forms of judgement as well, which we shall meet in due course. Now,
the question, What is a judgement? is no small question, because the
notion of judgement is just about the first of all the notions of logic,
the one that has to be explained before all the others, before even the
notions of proposition and truth, for instance. There is therefore an
intimate relation between the answer to the question what a judgement
is and the very question what logic itself is. I shall start by giving a
very simple answer, which is essentially right: after some elaboration,
at least, I hope that we shall have a sufficiently clear understanding of
it. And the definition would simply be that, when understood as an act
of judging, a judgement is nothing but an act of knowing, and, when
understood as that which is judged, it is a piece or, more solemnly, an
object of knowledge.

judgement
z ""-- -

the act of judging that which is judged
the act of knowing the object of knowledge

Thus, first of all, we have the ambiguity of the term judgement between
the act of judging and that which is judged. What I say is that an act

20 per martin-l"of
of judging is essentially nothing but an act of knowing, so that to judge
is the same as to know, and that what is judged is a piece, or an object,
of knowledge. Unfortunately, the English language has no counterpart
of Ger. eine Erkenntnis, a knowledge.

This new definition of the notion of judgement, so central to logic,
should be attributed in the first place to Kant, I think, although it may
be difficult to find him ever explicitly saying that the act of judging is
the same as the act of knowing, and that what is judged is the object of
knowledge. Nevertheless, it is behind all of Kant's analysis of the notion
of judgement that to judge amounts to the same as to know. It was
he who broke with the traditional, Aristotelian definition of judgement
as an affirmation or a denial. Explicitly, the notions of judgement
and knowledge were related by Bolzano, who simply defined knowledge
as evident judgement. Thus, for him, the order of priority was the
reverse: knowledge was defined in terms of judgement rather than the
other way round. The important thing to realize is of course that to
judge and to know, and, correlatively, judgement and knowledge, are
essentially the same. And, when the relation between judgement, or
assertion, if you prefer, and knowledge is understood in this way, logic
itself is naturally understood as the theory of knowledge, that is, of
demonstrative knowledge, Aristotle's a^pista*mh C'podeiktika*. Thus logic
studies, from an objective point of view, our pieces of knowledge as
they are organized in demonstrative science, or, if you think about it
from the act point of view, it studies our acts of judging, or knowing,
and how they are interrelated.

As I said a moment ago, this is only a first approximation, because
it would actually have been better if I had not said that an act of
judging is an act of knowing, but if I had said that it is an act of, and
here there are many words that you may use, either understanding,
or comprehending, or grasping, or seeing, in the metaphorical sense
of the word see in which it is synonymous with understand. I would
prefer this formulation, because the relation between the verb to know
and the verb to understand, comprehend, grasp, or see, is given by the
equation

to know = to have understood, comprehended, grasped, seen,
which has the converse

to understand, comprehend, grasp, see = to get to know.
The reason why the first answer needs elaboration is that you may
use know in English both in the sense of having understood and in
the sense of getting to understand. Now, the first of the preceding

on the meanings of the logical constants 21
two equations brings to expression something which is deeply rooted
in the Indo-European languages. For instance, Gr. oU'da, I know, is the
perfect form of the verb whose present form is Gr. eO`dw, I see. Thus
to know is to have seen merely by the way the verb has been formed
in Greek. It is entirely similar in Latin. You have Lat. nosco, I get to
know, which has present form, and Lat. novi, I know, which has perfect
form. So, in these and other languages, the verb to know has present
sense but perfect form. And the reason for the perfect form is that to
know is to have seen. Observe also the two metaphors for the act of
understanding which you seem to have in one form or the other in all
European languages: the metaphor of seeing, first of all, which was so
much used by the Greeks, and which we still use, for instance, when
saying that we see that there are infinitely many prime numbers, and,
secondly, the metaphor of grasping, which you also find in the verb to
comprehend, derived as it is from Lat. prehendere, to seize. The same
metaphor is found in Ger. fassen and begreifen, and I am sure that you
also have it in Italian. (Chorus. Afferare!) Of course, these are two
metaphors that we use for this particular act of the mind: the mental
act of understanding is certainly as different from the perceptual act
of seeing something as from the physical act of grasping something.

Is a judgement a judgement already before it is grasped, that is,
becomes known, or does it become a judgement only through our act
of judging? And, in the latter case, what should we call a judgement
before it has been judged, that is, has become known? For example, if
you let G be the proposition that every even number is the sum of two
prime numbers, and then look at

G is true,
is it a judgement, or is it not a judgement? Clearly, in one sense, it
is, and, in another sense, it is not. It is not a judgement in the sense
that it is not known, that is, that it has not been proved, or grasped.
But, in another sense, it is a judgement, namely, in the sense that G
is true makes perfectly good sense, because G is a proposition which
we all understand, and, presumably, we understand what it means
for a proposition to be true. The distinction I am hinting at is the
distinction which was traditionally made between an enunciation and a
proposition. Enunciation is not a word of much currency in English, but
I think that its Italian counterpart has fared better. The origin is the
Gr. C'pi`fansij as it appears in De Interpretatione, the second part of
the Organon. It has been translated into Lat. enuntiatio, It. enunciato,
and Ger. Aussage. An enunciation is what a proposition, in the old
sense of the word, is before it has been proved, or become known. Thus

22 per martin-l"of
it is a proposition stripped of its epistemic force. For example, in this
traditional terminology, which would be fine if it were still living, G is
true is a perfectly good enunciation, but it is not a proposition, not yet
at least. But now that we have lost the term proposition in its old sense,
having decided to use it in the sense in which it started to be used by
Russell and is now used in Anglo-Saxon philosophy and modern logic,
I think we must admit that we have also lost the traditional distinction
between an enunciation and a proposition. Of course, we still have
the option of keeping the term enunciation, but it is no longer natural.
Instead, since I have decided to replace the term proposition in its old
sense, as that which we prove and which may appear as premise or
conclusion of a logical inference, by the term judgement, as it has been
used in German philosophy from Kant and onwards, it seems better,
when there is a need of making the distinction between an enunciation
and a proposition, that is, between a judgement before and after it has
been proved, or become known, to speak of a judgement and an evident
judgement, respectively. This is a wellestablished usage in the writings
of Bolzano, Brentano, and Husserl, that is, within the objectivistically
oriented branch of German philosophy that I mentioned earlier. If we
adopt this terminology, then we are faced with a fourfold table, which
I shall end by writing up.

judgement proposition
evident judgement true proposition

Thus, correlated with the distinction between judgement and proposition, there is the distinction between evidence of a judgement and
truth of a proposition.

So far, I have said very little about the notions of proposition and
truth. The essence of what I have said is merely that to judge is the
same as to know, so that an evident judgement is the same as a piece,
or an object, of knowledge, in agreement with Bolzano's definition of
knowledge as evident judgement. Tomorrow's lecture will have to be
taken up by an attempt to clarify the notion of evidence and the notions
of proposition and truth.

Second lecture
Under what condition is it right, or correct, to make a judgement,
one of the form

A is true,

on the meanings of the logical constants 23
which is certainly the most basic form of judgement, for instance?
When one is faced with this question for the first time, it is tempting to answer simply that it is right to say that A is true provided that
A is true, and that it is wrong to say that A is true provided that A is
not true, that is, provided that A is false. In fact, this is what Aristotle
says in his definition of truth in the Metaphysics. For instance, he says
that it is not because you rightly say that you are white that you are
white, but because you are white that what you say is correct. But a
moment's reflection shows that this first answer is simply wrong. Even
if every even number is the sum of two prime numbers, it is wrong of
me to say that unless I know it, that is, unless I have proved it. And it
would have been wrong of me to say that every map can be coloured
by four colours before the recent proof was given, that is, before I acquired that knowledge, either by understanding the proof myself, or
by trusting its discoverers. So the condition for it to be right of me to
affirm a proposition A, that is, to say that A is true, is not that A is
true, but that I know that A is true. This is a point which has been
made by Dummett and, before him, by Brentano, who introduced the
apt term blind judgement for a judgement which is made by someone
who does not know what he is saying, although what he says is correct
in the weaker sense that someone else knows it, or, perhaps, that he
himself gets to know it at some later time. When you are forced into
answering a yes or no question, although you do not know the answer,
and happen to give the right answer, right as seen by someone else, or
by you yourself when you go home and look it up, then you make a
blind judgement. Thus you err, although the teacher does not discover
your error. Not to speak of the fact that the teacher erred more greatly
by not giving you the option of giving the only the answer which would
have been honest, namely, that you did not know.

The preceding consideration does not depend on the particular form
of judgement, in this case, A is true, that I happened to use as an
example. Quite generally, the condition for it to be right of you to
make a judgement is that you know it, or, what amounts to the same,
that it is evident to you. The notion of evidence is related to the notion
of knowledge by the equation

evident = known.
When you say that a judgement is evident, you merely express that
you have understood, comprehended, grasped, or seen it, that is, that
you know it, because to have understood is to know. This is reflected
in the etymology of the word evident, which comes from Lat. ex, out
of, from, and videre, to see, in the metaphorical sense, of course.

24 per martin-l"of

There is absolutely no question of a judgement being evident in
itself, independently of us and our cognitive activity. That would be
just as absurd as to speak of a judgement as being known, not by
somebody, you or me, but in itself. To be evident is to be evident to
somebody, as inevitably as to be known is to be known by somebody.
That is what Brouwer meant by saying, in Consciousness, Philosophy,
and Mathematics, that there are no nonexperienced truths, a basic
intuitionistic tenet. This has been puzzling, because it has been understood as referring to the truth of a proposition, and clearly there are
true propositions whose truth has not been experienced, that is, propositions which can be shown to be true in the future, although they have
not been proved to be true now. But what Brouwer means here is not
that. He does not speak about propositions and truth: he speaks about
judgements and evidence, although he uses the term truth instead of
the term evidence. And what he says is then perfectly right: there is
no evident judgement whose evidence has not been experienced, and
experience it is what you do when you understand, comprehend, grasp,
or see it. There is no evidence outside our actual or possible experience of it. The notion of evidence is by its very nature subject related,
relative to the knowing subject, that is, in Kantian terminology.

As I already said, when you make, or utter, a judgement under
normal circumstances, you thereby express that you know it. There is
no need to make this explicit by saying,

I know that . . .
For example, when you make a judgement of the form

A is true
under normal circumstances, by so doing, you already express that you
know that A is true, without having to make this explicit by saying,

I know that A is true,
or the like. A judgement made under normal circumstances claims by
itself to be evident: it carries its claim of evidence automatically with
it. This is a point which was made by Wittgenstein in the Tractatus
by saying that Frege's Urteilsstrich, judgement stroke, is logically quite
meaningless, since it merely indicates that the proposition to which it
is prefixed is held true by the author, although it would perhaps have
been better to say, not that it is meaningless, but that it is superfluous,
since, when you make a judgement, it is clear already from its form that
you claim to know it. In speech act philosophy, this is expressed by

on the meanings of the logical constants 25
saying that knowing is an illocutionary force: it is not an explicit part
of what you say that you know it, but it is implicit in your saying of
it. This is the case, not only with judgements, that is, acts of knowing,
but also with other kinds of acts. For instance, if you say,

Would she come tonight!
it is clear from the form of your utterance that you express a wish.
There is no need of making this explicit by saying,

I wish that she would come tonight.
Some languages, like Greek, use the optative mood to make it clear
that an utterance expresses a wish or desire.

Consider the pattern that we have arrived at now,

I

act
z ""-- -know objectz ""-- -

A is true

Here the grammatical subject I refers to the subject, self, or ego, and
the grammatical predicate know to the act, which in this particular
case is an act of knowing, but might as well have been an act of conjecturing, doubting, wishing, fearing, etc. Thus the predicate know
indicates the modality of the act, that is, the way in which the subject
relates to the object, or the particular force which is involved, in this
case, the epistemic force. Observe that the function of the grammatical
moods, indicative, subjunctive, imperative, and optative, is to express
modalities in this sense. Finally, A is true is the judgement or, in general, the object of the act, which in this case is an object of knowledge,
but might have been an object of conjecture, doubt, wish, fear, etc.

The closest possible correspondence between the analysis that I am
giving and Frege's notation for a judgement

` A
is obtained by thinking of the vertical, judgement stroke as carrying
the epistemic force

I know . . .
and the horizontal, content stroke as expressing the affirmation

. . . is true.

26 per martin-l"of
Then it is the vertical stroke which is superfluous, whereas the horizontal stroke is needed to show that the judgement has the form of an
affirmation. But this can hardly be read out of Frege's own account of
the assertion sign: you have to read it into his text.

What is a judgement before it has become evident, or known? That
is, of the two, judgement and evident judgement, how is the first to be
defined? The characteristic of a judgement in this sense is merely that
it has been laid down what knowledge is expressed by it, that is, what
you must know in order to have the right to make, or utter, it. And
this is something which depends solely on the form of the judgement.
For example, if we consider the two forms of judgement

A is a proposition
and

A is true,
then there is something that you must know in order to have the right
to make a judgement of the first form, and there is something else
which you must know, in addition, in order to have the right to make
a judgement of the second form. And what you must know depends
in neither case on A, but only on the form of the judgement, . . . is
a proposition or . . . is true, respectively. Quite generally, I may say
that a judgement in this sense, that is, a not yet known, and perhaps
even unknowable, judgement, is nothing but an instance of a form
of judgement, because it is for the various forms of judgement that
I lay down what you must know in order to have the right to make
a judgement of one of those forms. Thus, as soon as something has
the form of a judgement, it is already a judgement in this sense. For
example, A is a proposition is a judgement in this sense, because it
has a form for which I have laid down, or rather shall lay down, what
you must know in order to have the right to make a judgement of that
form. I think that I may make things a bit clearer by showing again
in a picture what is involved here. Let me take the first form to begin
with.

I

evident judgement
z ""-- -

know

judgement
z ""-- -\Upsilon

\Sigma

\Xi
\Pi
\Lambda
\Theta

\Gamma
\Delta A is a proposition

expression\Delta \Delta  form of judgementA

on the meanings of the logical constants 27
Here is involved, first, an expression A, which should be a complete
expression. Second, we have the form . . . is a proposition, which is
the form of judgement. Composing these two, we arrive at A is a
proposition, which is a judgement in the first sense. And then, third,
we have the act in which I grasp this judgement, and through which it
becomes evident. Thus it is my act of grasping which is the source of
the evidence. These two together, that is, the judgement and my act
of grasping it, become the evident judgement. And a similar analysis
can be given of a judgement of the second form.

I

evident judgement
z ""-- -

know

judgement
z ""-- -\Upsilon

\Sigma

\Xi
\Pi
\Lambda
\Theta

\Gamma
\Delta A is true

proposition\Delta \Delta  form of judgementA
Such a judgement has the form . . . is true, but what fills the open place,
or hole, in the form is not an expression any longer, but a proposition.
And what is a proposition? A proposition is an expression for which
the previous judgement has already been grasped, because there is no
question of something being true unless you have previously grasped it
as a proposition. But otherwise the picture remains the same here.

Now I must consider the discussion of the notion of judgement finished and pass on to the notion of proof. Proof is a good word, because,
unlike the word proposition, it has not changed its meaning. Proof apparently means the same now as it did when the Greeks discovered
the notion of proof, and therefore no terminological difficulties arise.
Observe that both Lat. demonstratio and the corresponding words in
the modern languages, like It. dimostrazione, Eng. demonstration, and
Ger. Beweis, are literal translations of Gr. C'pi`deicij, deriving as it does
from Gr. deDHknumi, I show, which has the same meaning as Lat. monstrare and Ger. weisen.

If you want to have a first approximation to the notion of proof, a
first definition of what a proof is, the strange thing is that you cannot look it up in any modern textbook of logic, because what you get
out of the standard textbooks of modern logic is the definition of what
a formal proof is, at best with a careful discussion clarifying that a
formal proof in the sense of this definition is not what we ordinarily
call a proof in mathematics. That is, you get a formal proof defined
as a finite sequence of formulas, each one of them being an immediate
consequence of some of the preceding ones, where the notion of immediate consequence, in turn, is defined by saying that a formula is an

28 per martin-l"of
immediate consequence of some other formulas if there is an instance
of one of the figures, called rules of inference, which has the other formulas as premises and the formula itself as conclusion. Now, this is not
what a real proof is. That is why you have the warning epithet formal
in front of it, and do not simply say proof.

What is a proof in the original sense of the word? The ordinary
dictionary definition says, with slight variations, that a proof is that
which establishes the truth of a statement. Thus a proof is that which
makes a mathematical statement, or enunciation, into a theorem, or
proposition, in the old sense of the word which is retained in mathematics. Now, remember that I have reserved the term true for true
propositions, in the modern sense of the word, and that the things
that we prove are, in my terminology, judgements. Moreover, to avoid
terminological confusion, judgements qualify as evident rather than
true. Hence, translated into the terminology that I have decided upon,
the dictionary definition becomes simply,

A proof is what makes a judgement evident.
Accepting this, that is, that the proof of a judgement is that which
makes it evident, we might just as well say that the proof of a judgement is the evidence for it. Thus proof is the same as evidence. Combining this with the outcome of the previous discussion of the notion of
evidence, which was that it is the act of understanding, comprehending, grasping, or seeing a judgement which confers evidence on it, the
inevitable conclusion is that the proof of a judgement is the very act
of grasping it. Thus a proof is, not an object, but an act. This is what
Brouwer wanted to stress by saying that a proof is a mental construction, because what is mental, or psychic, is precisely our acts, and the
word construction, as used by Brouwer, is but a synonym for proof.
Thus he might just as well have said that the proof of a judgement is
the act of proving, or grasping, it. And the act is primarily the act as it
is being performed. Only secondarily, and irrevocably, does it become
the act that has been performed.

As is often the case, it might have been better to start with the verb
rather than the noun, in this case, with the verb to prove rather than
with the noun proof. If a proof is what makes a judgement evident,
then, clearly, to prove a judgement is to make it evident, or known.
To prove something to yourself is simply to get to know it. And to
prove something to someone else is to try to get him, or her, to know
it. Hence

to prove = to get to know = to understand,
comprehend, grasp, or see.

on the meanings of the logical constants 29
This means that prove is but another synonym for understand, comprehend, grasp, or see. And, passing to the perfect tense,

to have proved = to know = to have understood,
comprehended, grasped, or seen.

We also speak of acquiring and possessing knowledge. To possess
knowledge is the same as to have acquired it, just as to know something
is the same as to have understood, comprehended, grasped, or seen it.
Thus the relation between the plain verb to know and the venerable
expressions to acquire and to possess knowledge is given by the two
equations,

to get to know = to acquire knowledge
and

to know = to possess knowledge.
On the other hand, the verb to prove and the noun proof are related
by the two similar equations,

to prove = to acquire, or construct, a proof
and

to have proved = to possess a proof.
It is now manifest, from these equations, that proof and knowledge are
the same. Thus, if proof theory is construed, not in Hilbert's sense,
as metamathematics, but simply as the study of proofs in the original
sense of the word, then proof theory is the same as theory of knowledge,
which, in turn, is the same as logic in the original sense of the word, as
the study of reasoning, or proof, not as metamathematics.

Remember that the proof of a judgement is the very act of knowing
it. If this act is atomic, or indivisible, then the proof is said to be immediate. Otherwise, that is, if the proof consists of a whole sequence,
or chain, of atomic actions, it is mediate. And, since proof and knowledge are the same, the attributes immediate and mediate apply equally
well to knowledge. In logic, we are no doubt more used to saying of
inferences, rather than proofs, that they are immediate or mediate, as
the case may be. But that makes no difference, because inference and
proof are the same. It does not matter, for instance, whether we say
rules of inference or proof rules, as has become the custom in programming. And, to take another example, it does not matter whether we
say that a mediate proof is a chain of immediate inferences or a chain

30 per martin-l"of
of immediate proofs. The notion of formal proof that I referred to in
the beginning of my discussion of the notion of proof has been arrived
at by formalistically interpreting what you mean by an immediate inference, by forgetting about the difference between a judgement and
a proposition, and, finally, by interpreting the notion of proposition
formalistically, that is, by replacing it by the notion of formula. But a
real proof is and remains what it has always been, namely, that which
makes a judgement evident, or simply, the evidence for it. Thus, if we
do not have the notion of evidence, we do not have the notion of proof.
That is why the notion of proof has fared so badly in those branches
of philosophy where the notion of evidence has fallen into disrepute.

We also speak of a judgement being immediately and mediately
evident, respectively. Which of the two is the case depends of course on
the proof which constitutes the evidence for the judgement. If the proof
is immediate, then the judgement is said to be immediately evident.
And an immediately evident judgement is what we call an axiom. Thus
an axiom is a judgement which is evident by itself, not by virtue of
some previously proved judgements, but by itself, that is, a self-evident
judgement, as one has always said. That is, always before the notion
of evidence became disreputed, in which case the notion of axiom and
the notion of proof simply become deflated: we cannot make sense
of the notion of axiom and the notion of proof without access to the
notion of evidence. If, on the other hand, the proof which constitutes
the evidence for a judgement is a mediate one, so that the judgement
is evident, not by itself, but only by virtue of some previously proved
judgements, then the judgement is said to be mediately evident. And
a mediately evident judgement is what we call a theorem, as opposed
to an axiom. Thus an evident judgement, that is, a proposition in the
old sense of the word which is retained in mathematics, is either an
axiom or a theorem.

Instead of applying the attributes immediate and mediate to proof,
or knowledge, I might have chosen to speak of intuitive and discursive
proof, or knowledge, respectively. That would have implied no difference of sense. The proof of an axiom can only be intuitive, which is
to say that an axiom has to be grasped immediately, in a single act.
The word discursive, on the other hand, comes from Lat. discurrere,
to run to and fro. Thus a discursive proof is one which runs, from
premises to conclusion, in several steps. It is the opposite of an intuitive proof, which brings you to the conclusion immediately, in a single
step. When one says that the immediate propositions in the old sense
of the word proposition, that is, the immediately evident judgements
in my terminology, are unprovable, what is meant is of course only that

on the meanings of the logical constants 31
they cannot be proved discursively. Their proofs have to rest intuitive.
This seems to be all that I have to say about the notion of proof at the
moment, so let me pass on to the next item on the agenda, the forms
of judgement and their semantical explanations.

The forms of judgement have to be displayed in a table, simply,
and the corresponding semantical explanations have to be given, one
for each of those forms. A form of judgement is essentially just what
is called a category, not in the sense of category theory, but in the
logical, or philosophical, sense of the word. Thus I have to say what
my forms of judgement, or categories, are, and, for each one of those
forms, I have to explain what you must know in order to have the right
to make a judgement of that form. By the way, the forms of judgement
have to be introduced in a specific order. Actually, not only the forms
of judgement, but all the notions that I am undertaking to explain
here have to come in a specific order. Thus, for instance, the notion
of judgement has to come before the notion of proposition, and the
notion of logical consequence has to be dealt with before explaining
the notion of implication. There is an absolute rigidity in this order.
The notion of proof, for instance, has to come precisely where I have
put it here, because it is needed in some other explanations further on,
where it is presupposed already. Revealing this rigid order, thereby
arriving eventually at the concepts which have to be explained prior
to all other concepts, turns out to be surprisingly difficult: you seem
to arrive at the very first concepts last of all. I do not know what
it should best be called, maybe the order of conceptual priority, one
concept being conceptually prior to another concept if it has to be
explained before the other concept can be explained.

Let us now consider the first form of judgement,

A is a proposition,
or, as I shall continue to abbreviate it,

A prop.
What I have just displayed to you is a linguistic form, and I hope that
you can recognize it. What you cannot see from the form, and which
I therefore proceed to explain to you, is of course its meaning, that is,
what knowledge is expressed by, or embodied in, a judgement of this
form. The question that I am going to answer is, in ontological terms,

What is a proposition?
This is the usual Socratic way of formulating questions of this sort. Or
I could ask, in more knowledge theoretical terminology,

32 per martin-l"of

What is it to know a proposition?
or, if you prefer,

What knowledge is expressed by a judgement
of the form A is a proposition?

or, this may be varied endlessly,

What does a judgement of the form A is a proposition mean?
These various ways of posing essentially the same question reflect
roughly the historical development, from a more ontological to a more
knowledge theoretical way of posing, and answering, questions of this
sort, finally ending up with something which is more linguistic in nature, having to do with form and meaning.

Now, one particular answer to this question, however it be formulated, is that a proposition is something that is true or false, or, to use
Aristotle's formulation, that has truth or falsity in it. Here we have
to be careful, however, because what I am going to explain is what a
proposition in the modern sense is, whereas what Aristotle explained
was what an enunciation, being the translation of Gr. C'pi`fansij, is.
And it was this explanation that he phrased by saying that an enunciation is something that has truth or falsity in it. What he meant by
this was that it is an expression which has a form of speech such that,
when you utter it, you say something, whether truly or falsely. That
is certainly not how we now interpret the definition of a proposition as
something which is true or false, but it is nevertheless correct that it
echoes Aristotle's formulation, especially in its symmetric treatment of
truth and falsity.

An elaboration of the definition of a proposition as something that
is true or false is to say that a proposition is a truth value, the true
or the false, and hence that a declarative sentence is an expression
which denotes a truth value, or is the name of a truth value. This
was the explanation adopted by Frege in his later writings. If a proposition is conceived in this way, that is, simply as a truth value, then
there is no difficulty in justifying the laws of the classical propositional
calculus and the laws of quantification over finite, explicitly listed, domains. The trouble arises when you come to the laws for forming
quantified propositions, the quantifiers not being restricted to finite
domains. That is, the trouble is to make the two laws

A(x) prop
(8x)A(x) prop

A(x) prop
(9x)A(x) prop

on the meanings of the logical constants 33
evident when propositions are conceived as nothing but truth values.
To my mind, at least, they simply fail to be evident. And I need not
be ashamed of the reference to myself in this connection: as I said
in my discussion of the notion of evidence, it is by its very nature
subject related. Others must make up their minds whether these laws
are really evident to them when they conceive of propositions simply
as truth values. Although we have had this notion of proposition and
these laws for forming quantified propositions for such a long time,
we still have no satisfactory explanations which serve to make them
evident on this conception of the notion of proposition. It does not
help to restrict the quantifiers, that is, to consider instead the laws

(x 2 A)
B(x) prop
(8x 2 A)B(x) prop

(x 2 A)
B(x) prop
(9x 2 A)B(x) prop

unless we restrict the quantifiers so severely as to take the set A here
to be a finite set, that is, to be given by a list of its elements. Then, of
course, there is no trouble with these rules. But, as soon as A is the set
of natural numbers, say, you have the full trouble already. Since, as I
said earlier, the law of the excluded middle, indeed, all the laws of the
classical propositional calculus, are doubtlessly valid on this conception
of the notion of proposition, this means that the rejection of the law
of excluded middle is implicitly also a rejection of the conception of a
proposition as something which is true or false. Hence the rejection of
this notion of proposition is something which belongs to Brouwer. On
the other hand, he did not say explicitly by what it should be replaced.
Not even the wellknown papers by Kolmogorov and Heyting, in which
the formal laws of intuitionistic logic were formulated for the first time,
contain any attempt at explaining the notion of proposition in terms of
which these laws become evident. It appears only in some later papers
by Heyting and Kolmogorov from the early thirties. In the first of these,
written by Heyting in 1930, he suggested that we should think about
a proposition as a problem, Fr. probl`eme, or expectation, Fr. attente.
And, in the wellknown paper of the following year, which appeared
in Erkenntnis, he used the terms expectation, Ger. Erwartung, and
intention, Ger. Intention. Thus he suggested that one should think of
a proposition as a problem, or as an expectation, or as an intention.
And, another year later, there appeared a second paper by Kolmogorov,
in which he observed that the laws of the intuitionistic propositional
calculus become evident upon thinking of the propositional variables
as ranging over problems, or tasks. The term he actually used was

34 per martin-l"of
Ger. Aufgabe. On the other hand, he explicitly said that he did not
want to equate the notion of proposition with the notion of problem
and, correlatively, the notion of truth of a proposition with the notion
of solvability of a problem. He merely proposed the interpretation of
propositions as problems, or tasks, as an alternative interpretation,
validating the laws of the intuitionistic propositional calculus.

Returning now to the form of judgement

A is a proposition,
the semantical explanation which goes together with it is this, and here
I am using the knowledge theoretical formulation, that to know a proposition, which may be replaced, if you want, by problem, expectation,
or intention, you must know what counts as a verification, solution,
fulfillment, or realization of it. Here verification matches with proposition, solution with problem, fulfillment with expectation as well as
with intention, and realization with intention. Realization is the term
introduced by Kleene, but here I am of course not using it in his sense:
Kleene's realizability interpretation is a nonstandard, or nonintended,
interpretation of intuitionistic logic and arithmetic. The terminology
of intention and fulfillment was taken over by Heyting from Husserl, via
Oskar Becker, apparently. There is a long chapter in the sixth, and last,
of his Logische Untersuchungen which bears the title Bedeutungsintention und Bedeutungserf"ullung, and it is these two terms, intention and
fulfillment, Ger. Erf"ullung, that Heyting applied in his analysis of the
notions of proposition and truth. And he did not just take the terms
from Husserl: if you observe how Husserl used these terms, you will see
that they were appropriately applied by Heyting. Finally, verification
seems to be the perfect term to use together with proposition, coming
as it does from Lat. verus, true, and facere, to make. So to verify is to
make true, and verification is the act, or process, of verifying something.
For a long time, I tried to avoid using the term verification, because
it immediately gives rise to discussions about how the present account
of the notions of proposition and truth is related to the verificationism
that was discussed so much in the thirties. But, fortunately, this is fifty
years ago now, and, since we have a word which lends itself perfectly
to expressing what needs to be expressed, I shall simply use it, without
wanting to get into discussion about how the present semantical theory
is related to the verificationism of the logical positivists.

What would an example be? If you take a proposition like,

The sun is shining,

on the meanings of the logical constants 35
to know that proposition, you must know what counts as a verification
of it, which in this case would be the direct seeing of the shining sun.
Or, if you take the proposition,

The temperature is 10ffi C,
then it would be a direct thermometer reading. What is more interesting, of course, is what the corresponding explanations look like for the
logical operations, which I shall come to in my last lecture.

Coupled with the preceding explanation of what a proposition is, is
the following explanation of what a truth is, that is, of what it means
for a proposition to be true. Assume first that

A is a proposition,
and, because of the omnipresence of the epistemic force, I am really
asking you to assume that you know, that is, have grasped, that A
is a proposition. On that assumption, I shall explain to you what a
judgement of the form

A is true,
or, briefly,

A true,
means, that is, what you must know in order to have the right to
make a judgement of this form. And the explanation would be that, to
know that a proposition is true, a problem is solvable, an expectation
is fulfillable, or an intention is realizable, you must know how to verify,
solve, fulfill, or realize it, respectively. Thus this explanation equates
truth with verifiability, solvability, fulfillability, or realizability. The
important point to observe here is the change from is in A is true to
can in A can be verified, or A is verifiable. Thus what is expressed in
terms of being in the first formulation really has the modal character
of possibility.

Now, as I said earlier in this lecture, to know a judgement is the
same as to possess a proof of it, and to know a judgement of the
particular form A is true is the same as to know how, or be able, to
verify the proposition A. Thus knowledge of a judgement of this form
is knowledge how in Ryle's terminology. On the other hand, to know
how to do something is the same as to possess a way, or method, of
doing it. This is reflected in the etymology of the word method, which
is derived from Gr. metL', after, and a*di`j, way. Taking all into account,
we arrive at the conclusion that a proof that a proposition A is true

36 per martin-l"of
is the same as a method of verifying, solving, fulfilling, or realizing A.
This is the explanation for the frequent appearance of the word method
in Heyting's explanations of the meanings of the logical constants. In
connection with the word method, notice the tendency of our language
towards hypostatization. I can do perfectly well without the concept of
method in my semantical explanations: it is quite sufficient for me to
have access to the expression know how, or knowledge how. But it is in
the nature of our language that, when we know how to do something,
we say that we possess a method of doing it.

Summing up, I have now explained the two forms of categorical
judgement,

A is a proposition
and

A is true,
respectively, and they are the only forms of categorical judgement that
I shall have occasion to consider. Observe that knowledge of a judgement of the second form is knowledge how, more precisely, knowledge
how to verify A, whereas knowledge of a judgement of the first form
is knowledge of a problem, expectation, or intention, which is knowledge what to do, simply. Here I am introducing knowledge what as a
counterpart of Ryle's knowledge how. So the difference between these
two kinds of knowledge is the difference between knowledge what to do
and knowledge how to do it. And, of course, there can be no question
of knowing how to do something before you know what it is that is to
be done. The difference between the two kinds of knowledge is a categorical one, and, as you see, what Ryle calls knowledge that, namely,
knowledge that a proposition is true, is equated with knowledge how
on this analysis. Thus the distinction between knowledge how and
knowledge that evaporates on the intuitionistic analysis of the notion
of truth.

Third lecture
The reason why I said that the word verification may be dangerous
is that the principle of verification formulated by the logical positivists
in the thirties said that a proposition is meaningful if and only if it is
verifiable, or that the meaning of a proposition is its method of verification. Now that is to confuse meaningfulness and truth. I have
indeed used the word verifiable and the expression method of verification. But what is equated with verifiability is not the meaningfulness

on the meanings of the logical constants 37
but the truth of a proposition, and what qualifies as a method of verification is a proof that a proposition is true. Thus the meaning of a
proposition is not its method of verification. Rather, the meaning of a
proposition is determined by what it is to verify it, or what counts as
a verification of it.

The next point that I want to bring up is the question,

Are there propositions which are true,
but which cannot be proved to be true?

And it suffices to think of mathematical propositions here, like the
Goldbach conjecture, the Riemann hypothesis, or Fermat's last theorem. This fundamental question was once posed to me outright by a
colleague of mine in the mathematics department, which shows that
even working mathematicians may find themselves puzzled by deep
philosophical questions. At first sight, at least, there seem to be two
possible answers to this question. One is simply,

No,
and the other is,

Perhaps,
although it is of course impossible for anybody to exhibit an example
of such a proposition, because, in order to do that, he would already
have to know it to be true. If you are at all puzzled by this question,
it is an excellent subject of meditation, because it touches the very
conflict between idealism and realism in the theory of knowledge, the
first answer, No, being indicative of idealism, and the second answer,
Perhaps, of realism. It should be clear, from any point of view, that
the answer depends on how you interpret the three notions in terms
of which the question is formulated, that is, the notion of proposition,
the notion of truth, and the notion of proof. And it should already be
clear, I believe, from the way in which I have explained these notions,
that the question simply ceases to be a problem, and that it is the first
answer which is favoured.

To see this, assume first of all that A is a proposition, or problem.
Then

A is true
is a judgement which gives rise to a new problem, namely, the problem
of proving that A is true. To say that that problem is solvable is precisely the same as saying that the judgement that A is true is provable.
Now, the solvability of a problem is always expressed by a judgement.
Hence

38 per martin-l"of

(A is true) is provable
is a new judgement. What I claim is that we have the right to make this
latter judgement if and only if we have the right to make the former
judgement, that is, that the proof rule

A is true
(A is true) is provable

as well as its inverse

(A is true) is provable

A is true

are both valid. This is the sense of saying that A is true if and only if
A can be proved to be true. To justify the first rule, assume that you
know its premise, that is, that you have proved that A is true. But, if
you have proved that A is true, then you can, or know how to, prove
that A is true, which is what you need to know in order to have the
right to judge the conclusion. In this step, I have relied on the principle
that, if something has been done, then it can be done. To justify the
second rule, assume that you know its premise, that is, that you know
how to prove the judgement A is true. On that assumption, I have to
explain the conclusion to you, which is to say that I have to explain
how to verify the proposition A. This is how you do it. First, put your
knowledge of the premise into practice. That yields as result a proof
that A is true. Now, such a proof is nothing but knowledge how to
verify, or a method of verifying, the proposition A. Hence, putting it,
in turn, into practice, you end up with a verification of the proposition
A, as required. Observe that the inference in this direction is essentially
a contraction of two possibilities into one: if you know how to know
how to do something, then you know how to do it.

All this is very easy to say, but, if one is at all puzzled by the question whether there are unprovable truths, then it is not an easy thing to
make up one's mind about. For instance, it seems, from Heyting's writings on the semantics of intuitionistic logic in the early thirties, that
he had not arrived at this position at that time. The most forceful and
persistent criticism of the idea of a knowledge independent, or knowledge transcendent, notion of truth has been delivered by Dummett,
although it seems difficult to find him ever explicitly committing himself in his writings to the view that, if a proposition is true, then it can
also be proved to be true. Prawitz seems to be leaning towards this
nonrealistic principle of truth, as he calls it, in his paper Intuitionistic

on the meanings of the logical constants 39
Logic: A Philosophical Challenge. And, in his book Det Os"agbara,
printed in the same year, Stenlund explicitly rejects the idea of true
propositions that are in principle unknowable. The Swedish proof theorists seem to be arriving at a common philosophical position.

Next I have to say something about hypothetical judgements, before I proceed to the final piece, which consists of the explanations
of the meanings of the logical constants and the justifications of the
logical laws. So far, I have only introduced the two forms of categorical judgement A is a proposition and A is true. The only forms of
judgement that I need to introduce, besides these, are forms of hypothetical judgement. Hypothetical means of course the same as under
assumptions. The Gr. I'pi`qesij, hypothesis, was translated into Lat.
suppositio, supposition, and they both mean the same as assumption.
Now, what is the rule for making assumptions, quite generally? It is
simple. Whenever you have a judgement in the sense that I am using
the word, that is, a judgement in the sense of an instance of a form of
judgement, then it has been laid down what you must know in order
to have the right to make it. And that means that it makes perfectly
good sense to assume it, which is the same as to assume that you know
it, which, in turn, is the same as to assume that you have proved it.
Why is it the same to assume it as to assume that you know it? Because of the constant tacit convention that the epistemic force, I know
. . . , is there, even if it is not made explicit. Thus, when you assume
something, what you do is that you assume that you know it, that is,
that you have proved it. And, to repeat, the rule for making assumptions is simply this: whenever you have a judgement, in the sense of an
instance of a form of judgement, you may assume it. That gives rise
to the notion of hypothetical judgement and the notion of hypothetical
proof, or proof under hypotheses.

The forms of hypothetical judgement that I shall need are not so
many. Many more can be introduced, and they are needed for other
purposes. But what is absolutely necessary for me is to have access to
the form

A1 true; : : : ; An true j A prop;

which says that A is a proposition under the assumptions that
A1; : : : ; An are all true, and, on the other hand, the form

A1 true; : : : ; An true j A true;
which says that the proposition A is true under the assumptions that
A1; : : : ; An are all true. Here I am using the vertical bar for the relation
of logical consequence, that is, for what Gentzen expressed by means of

40 per martin-l"of
the arrow ! in his sequence calculus, and for which the double arrow
) is also a common notation. It is the relation of logical consequence,
which must be carefully distinguished from implication. What stands
to the left of the consequence sign, we call the hypotheses, in which
case what follows the consequence sign is called the thesis, or we call
the judgements that precede the consequence sign the antecedents and
the judgement that follows after the consequence sign the consequent.
This is the terminology which Gentzen took over from the scholastics,
except that, for some reason, he changed consequent into succedent and
consequence into sequence, Ger. Sequenz, usually improperly rendered
by sequent in English.

hypothetical judgement

(logical) consequence
z ""-- -

A1 true; : : : ; An true j A prop
A1 true; : : : ; An true j A true
-- -z "" -- -z ""

antecedents consequent

hypotheses thesis

Since I am making the assumptions A1 true; : : : ; An true, I must be
presupposing something here, because, surely, I cannot make those
assumptions unless they are judgements. Specifically, in order for A1
true to be a judgement, A1 must be a proposition, and, in order for
A2 true to be a judgement, A2 must be a proposition, but now merely
under the assumption that A1 is true, . . . , and, in order for An true
to be a judgement, An must be a proposition under the assumptions
that A1; : : : ; An\Gamma 1 are all true. Unlike in Gentzen's sequence calculus,
the order of the assumptions is important here. This is because of the
generalization that something being a proposition may depend on other
things being true. Thus, for the assumptions to make sense, we must
presuppose

A1 prop;
A1 true j A2 prop;

...

A1 true; : : : ; An\Gamma 1 true j An prop.
Supposing this, that is, supposing that we know this, it makes perfectly
good sense to assume, first, that A1 is true, second, that A2 is true,
. . . , finally, that An is true, and hence

A1 true; : : : ; An true j A prop

on the meanings of the logical constants 41
is a perfectly good judgement whatever expression A is, that is, whatever expression you insert into the place indicated by the variable A.
And why is it a good judgement? To answer that question, I must
explain to you what it is to know such a judgement, that is, what
constitutes knowledge, or proof, of such a judgement. Now, quite generally, a proof of a hypothetical judgement, or logical consequence, is
nothing but a hypothetical proof of the thesis, or consequent, from the
hypotheses, or antecedents. The notion of hypothetical proof, in turn,
which is a primitive notion, is explained by saying that it is a proof
which, when supplemented by proofs of the hypotheses, or antecedents,
becomes a proof of the thesis, or consequent. Thus the notion of categorical proof precedes the notion of hypothetical proof, or inference, in
the order of conceptual priority. Specializing this general explanation
of what a proof of a hypothetical judgement is to the particular form
of hypothetical judgement

A1 true; : : : ; An true j A prop
that we are in the process of considering, we see that the defining
property of a proof

A1 true \Delta  \Delta  \Delta  An true

\Delta \Delta \Delta  \Delta \Delta \Delta

A prop

of such a judgement is that, when it is supplemented by proofs

...

A1 true \Delta  \Delta  \Delta

...
An true
of the hypotheses, or antecedents, it becomes a proof

...

A1 true \Delta  \Delta  \Delta

...
An true
\Delta \Delta \Delta  \Delta \Delta \Delta

A prop

of the thesis, or consequent.

Consider now a judgement of the second form

A1 true; : : : ; An true j A true:
For it to make good sense, that is, to be a judgement, we must know,
not only

42 per martin-l"of

A1 prop;
A1 true j A2 prop;

...

A1 true; : : : ; An\Gamma 1 true j An prop;
as in the case of the previous form of judgement, but also

A1 true; : : : ; An true j A prop:
Otherwise, it does not make sense to ask oneself whether A is true
under the assumptions A1 true, . . . , An true. As with any proof of a
hypothetical judgement, the defining characteristic of a proof

A1 true \Delta  \Delta  \Delta  An true

\Delta \Delta \Delta  \Delta \Delta \Delta

A true

of a hypothetical judgement of the second form is that, when supplemented by proofs

...

A1 true \Delta  \Delta  \Delta

...
An true
of the antecedents, it becomes a categorical proof

...

A1 true \Delta  \Delta  \Delta

...
An true
\Delta \Delta \Delta  \Delta \Delta \Delta

A true

of the consequent.

I am sorry that I have had to be so brief in my treatment of hypothetical judgements, but what I have said is sufficient for the following,
except that I need to generalize the two forms of hypothetical judgement so as to allow generality in them. Thus I need judgements which
are, not only hypothetical, but also general, which means that the first
form is turned into

A1(x1; : : : ; xm) true; : : : ; An(x1; : : : ; xm) true jx1;:::;x

m A(x1; : : : ; xm) prop

and the second form into

A1(x1; : : : ; xm) true; : : : ; An(x1; : : : ; xm) true jx1;:::;x

m A(x1; : : : ; xm) true:

Both of these forms involve a generality, indicated by subscribing the
variables that are being generalized to the consequence sign, which
must be carefully distinguished from, and which must be explained

on the meanings of the logical constants 43
prior to, the generality which is expressed by means of the universal
quantifier. It was only to avoid introducing all complications at once
that I treated the case without generality first. Now, the meaning of
a hypothetico-general judgement is explained by saying that, to have
the right to make such a judgement, you must possess a free variable
proof of the thesis, or consequent, from the hypotheses, or antecedents.
And what is a free variable proof? It is a proof which remains a proof
when you substitute anything you want for its free variables, that is,
any expressions you want, of the same arities as those variables. Thus

A1(x1; : : : ; xm) true \Delta  \Delta  \Delta  An(x1; : : : ; xm) true

\Delta \Delta \Delta  \Delta \Delta \Delta

A(x1; : : : ; xm) prop

is a proof of a hypothetico-general judgement of the first form provided
it becomes a categorical proof

...

A1(a1; : : : ; am) true \Delta  \Delta  \Delta

...
An(a1; : : : ; am) true
\Delta \Delta \Delta  \Delta \Delta \Delta

A(a1; : : : ; am) prop

when you first substitute arbitrary expressions a1; : : : ; am, of the same
respective arities as the variables x1; : : : ; xm, for those variables, and
then supplement it with proofs

...

A1(a1; : : : ; am) true \Delta  \Delta  \Delta

...
An(a1; : : : ; am) true
of the resulting substitution instances of the antecedents. The explanation of what constitutes a proof of a hypothetico-general judgement
of the second form is entirely similar.

The difference between an inference and a logical consequence, or
hypothetical judgement, is that an inference is a proof of a logical consequence. Thus an inference is the same as a hypothetical proof. Now,
when we infer, or prove, we infer the conclusion from the premises.
Thus, just as a categorical proof is said to be a proof of its conclusion,
a hypothetical proof is said to be a proof, or an inference, of its conclusion from its premises. This makes it clear what is the connection
as well as what is the difference between an inference with its premises
and conclusion on the one hand, and a logical consequence with its
antecedents and consequent on the other hand. And the difference is
precisely that it is the presence of a proof of a logical consequence that

44 per martin-l"of
turns its antecedents into premises and the consequent into conclusion
of the proof in question. For example, if A is a proposition, then

A true j ? true
is a perfectly good logical consequence with A true as antecedent and
? true as consequent, but

A true

? true

is not an inference, not a valid inference, that is, unless A is false. In
that case, only, may the conclusion ? true be inferred from the premise
A true.

Let us now pass on to the rules of inference, or proof rules, and their
semantical explanations. I shall begin with the rules of implication.
Now, since I am treating A is a proposition as a form of judgement,
which is on a par with the form of judgement A is true, what we
ordinarily call formation rules will count as rules of inference, but that
is merely a terminological matter. So let us look at the formation rule
for implication.

oe-formation.

A prop

(A true)

B prop
A oe B prop

This rule says, in words, that, if A is a proposition and B is a proposition provided that A is true, then A oe B is a proposition. In the
second premise, I might just as well have used the notation for logical
consequence

A true j B prop

that I introduced earlier in this lecture, because to have a proof of
this logical consequence is precisely the same as to have a hypothetical
proof of B prop from the assumption A true. But, for the moment, I
shall use the more suggestive notation

(A true)

B prop

in imitation of Gentzen. It does not matter, of course, which notation
of the two that I employ. The meaning is in any case the same.

Explanation. The rule of implication formation is a rule of immediate inference, which means that you must make the conclusion evident

on the meanings of the logical constants 45
to yourself immediately, without any intervening steps, on the assumption that you know the premises. So assume that you do know the
premises, that is, that you know the proposition A, which is to say
that you know what counts as a verification of it, and that you know
that B is a proposition under the assumption that A is true. My obligation is to explain to you what proposition A oe B is. Thus I have
to explain to you what counts as a verification, or solution, of this
proposition, or problem. And the explanation is that what counts as a
verification of A oe B is a hypothetical proof

A true.

..

B true

that B is true under the assumption that A is true. In the Kolmogorov
interpretation, such a hypothetical proof appears as a method of solving
the problem B provided that the problem A can be solved, that is,
a method which together with a method of solving the problem A
becomes a method of solving the problem B. The explanation of the
meaning of implication, which has just been given, illustrates again the
rigidity of the order of conceptual priority: the notions of hypothetical
judgement, or logical consequence, and hypothetical proof have to be
explained before the notion of implication, because, when you explain
implication, they are already presupposed.

Given the preceding explanation of the meaning of implication, it
is not difficult to justify the rule of implication introduction.

oe-introduction. (A true)

B true
A oe B true

As you see, I am writing it in the standard way, although, of course, it
is still presupposed that A is a proposition and that B is a proposition
under the assumption that A is true. Thus you must know the premises
of the formation rule and the premise of the introduction rule in order
to be able to grasp its conclusion.

Explanation. Again, the rule of implication introduction is a rule of
immediate inference, which means that you must make the conclusion
immediately evident to yourself granted that you know the premises,
that is, granted that you possess a hypothetical proof that B is true
from the hypothesis that A is true. By the definition of implication,
such a proof is nothing but a verification of the proposition A oe B.
And what is it that you must know in order to have the right to judge

46 per martin-l"of
A oe B to be true? You must know how to get yourself a verification
of A oe B. But, since you already possess it, you certainly know how
to acquire it: just take what you already have. This is all that there
is to be seen in this particular rule. Observe that its justification rests
again on the principle that, if something has been done, then it can be
done.

Next we come to the elimination rule for implication, which I shall
formulate in the standard way, as modus ponens, although, if you want
all elimination rules to follow the same pattern, that is, the pattern
exhibited by the rules of falsehood, disjunction, and existence elimination, there is another formulation that you should consider, and which
has been considered by Schroeder-Heister. But I shall have to content
myself with the standard formulation in these lectures.

oe-elimination. A oe B true A true

B true
Here it is still assumed, of course, that A is a proposition and that B
is a proposition provided that A is true.

Explanation. This is a rule of immediate inference, so assume that
you know the premises, that is, that you possess proofs

...

A oe B true

and ...

A true

of them, and I shall try to make the conclusion evident to you. Now, by
the definitions of the notion of proof and the notion of truth, the proof
of the first premise is knowledge how to verify the proposition A oe B.
So put that knowledge of yours into practice. What you then end up
with is a verification of A oe B, and, because of the way implication
was defined, that verification is nothing but a hypothetical proof

A true.

..

B true

that B is true from the assumption that A is true. Now take your proof
of the right premise and adjoin it to the verification of A oe B. Then
you get a categorical proof ..

.
A true.

..

B true

on the meanings of the logical constants 47
of the conclusion that B is true. Here, of course, I am implicitly using
the principle that, if you supplement a hypothetical proof with proofs
of its hypotheses, then you get a proof of its conclusion. But this is in
the nature of a hypothetical proof: it is that property which makes a
hypothetical proof into what it is. So now you have a proof that B is
true, a proof which is knowledge how to verify B. Putting it, in turn,
into practice, you end up with a verification of B. This finishes my
explanation of how the proposition B is verified.

In the course of my semantical explanation of the elimination rule
for implication, I have performed certain transformations which are
very much like an implication reduction in the sense of Prawitz. Indeed,
I have explained the semantical role of this syntactical transformation.
The place where it belongs in the meaning theory is precisely in the
semantical explanation, or justification, of the elimination rule for implication. Similarly, the reduction rules for the other logical constants
serve to explain the elimination rules associated with those constants.
The key to seeing the relationship between the reduction rules and
the semantical explanations of the elimination rules is this: to verify
a proposition by putting a proof of yours that it is true into practice
corresponds to reducing a natural deduction to introductory form and
deleting the last inference. This takes for granted, as is in fact the
case, that an introduction is an inference in which you conclude, from
the possession of a verification of a proposition, that you know how to
verify it. In particular, verifying a proposition B by means of a proof
that B is true ...

A oe B true

...
A true
B true

which ends with an application of modus ponens, corresponds to reducing the proof of the left premise to introductory form

(A true).

..

B true
A oe B true

...
A true
B true

then performing an implication reduction in the sense of Prawitz, which
yields the proof

48 per martin-l"of

...
A true.

..

B true

as result, and finally reducing the latter proof to introductory form
and deleting its last, introductory inference. This is the syntactical
counterpart of the semantical explanation of the elimination rule for
implication.

The justifications of the remaining logical laws follow the same pattern. Let me take the rules of conjunction next.

& -formation.

A prop B prop

A & B prop
Explanation. Again, assume that you know the premises, and I
shall explain the conclusion to you, that is, I shall tell you what counts
as a verification of A & B. The explanation is that a verification of
A & B consists of a proof that A is true and a proof that B is true,

...

A true

and ...

B true

that is, of a method of verifying A and a method of verifying B. In
the Kolmogorov interpretation, A & B appears as the problem which
you solve by constructing both a method of solving A and a method of
solving B.

& -introduction. A true B true

A & B true
Here the premises of the formation rule are still in force, although not
made explicit, which is to say that A and B are still assumed to be
propositions.

Explanation. Assume that you know the premises, that is, that you
possess proofs ..

.
A true

and ...

B true

of them. Because of the meaning of conjunction, just explained, this
means that you have verified A & B. Then you certainly can, or know
how to, verify the proposition A & B, by the principle that, if something
has been done, then it can be done. And this is precisely what you need
to know in order to have the right to judge A & B to be true.

on the meanings of the logical constants 49
If you want the elimination rule for conjunction to exhibit the same
pattern as the elimination rules for falsehood, disjunction, and existence, it should be formulated differently, but, in its standard formulation, it reads as follows.

& -elimination.

A & B true

A true

A & B true

B true

Thus, in this formulation, there are two rules and not only one. Also,
it is still presupposed, of course, that A and B are propositions.

Explanation. It suffices for me to explain one of the rules, say the
first, because the explanation of the other is completely analogous. To
this end, assume that you know the premise, and I shall explain to you
the conclusion, which is to say that I shall explain how to verify A.
This is how you do it. First use your knowledge of the premise to get a
verification of A & B. By the meaning of conjunction, just explained,
that verification consists of a proof that A is true as well as a proof
that B is true, ..

.
A true

and ...

B true

Now select the first of these two proofs. By the definitions of the
notions of proof and truth, that proof is knowledge how to verify A.
So, putting it into practice, you end up with a verification of A. This
finishes the explanations of the rules of conjunction.

The next logical operation to be treated is disjunction. And, as
always, the formation rule must be explained first.

.-formation.

A prop B prop

A . B prop

Explanation. To justify it, assume that you know the premises, that
is, that you know what it is to verify A as well as what it is to verify
B. On that assumption, I explain to you what proposition A . B is by
saying that a verification of A . B is either a proof that A is true or a
proof that B is true, ..

.
A true

or ...

B true

Thus, in the wording of the Kolmogorov interpretation, a solution to
the problem A . B is either a method of solving the problem A or a
method of solving the problem B.

50 per martin-l"of

.-introduction.

A true
A . B true

B true
A . B true

In both of these rules, the premises of the formation rule, which say
that A and B are propositions, are still in force.

Explanation. Assume that you know the premise of the first rule
of disjunction introduction, that is, that you have proved, or possess a
proof of, the judgement that A is true. By the definition of disjunction,
this proof is a verification of the proposition A . B. Hence, by the
principle that, if something has been done, then it can be done, you
certainly can, or know how to, verify the proposition A . B. And it is
this knowledge which you express by judging the conclusion of the rule,
that is, by judging the proposition A . B to be true. The explanation
of the second rule of disjunction introduction is entirely similar.

.-elimination.

A . B true

(A true)

C true

(B true)

C true
C true

Here it is presupposed, not only that A and B are propositions, but also
that C is a proposition provided that A . B is true. Observe that, in
this formulation of the rule of disjunction elimination, C is presupposed
to be a proposition, not outright, but merely on the hypothesis that
A . B is true. Otherwise, it is just like the Gentzen rule.

Explanation. Assume that you know, or have proved, the premises.
By the definition of truth, your knowledge of the first premise is knowledge how to verify the proposition A . B. Put that knowledge of yours
into practice. By the definition of disjunction, you then end up either
with a proof that A is true or with a proof that B is true,

...

A true

or ...

B true

In the first case, join the proof that A is true to the proof that you
already possess of the second premise, which is a hypothetical proof
that C is true under the hypothesis that A is true,

A true.

..

C true

You then get a categorical, or nonhypothetical, proof that C is true,

on the meanings of the logical constants 51

...
A true.

..

C true

Again, by the definition of truth, this proof is knowledge how to verify
the proposition C. So, putting this knowledge of yours into practice,
you verify C. In the second case, join the proof that B is true, which
you ended up with as a result of putting your knowledge of the first
premise into practice, to the proof that you already possess of the
third premise, which is a hypothetical proof that C is true under the
hypothesis that B is true,

B true.

..

C true

You then get a categorical proof that C is true,

...

B true.

..

C true

As in the first case, by the definition of truth, this proof is knowledge how to verify the proposition C. So, putting this knowledge into
practice, you verify C. This finishes my explanation how to verify the
proposition C, which is precisely what you need to know in order to
have the right to infer the conclusion that C is true.

?-formation.

? prop

Explanation. This is an axiom, but not in its capacity of mere
figure: to become an axiom, it has to be made evident. And, to make
it evident, I have to explain what counts as a verification of ?. The
explanation is that there is nothing that counts as a verification of
the proposition ?. Under no condition is it true. Thinking of ? as a
problem, as in the Kolmogorov interpretation, it is the problem which
is defined to have no solution.

An introduction is an inference in which you conclude that a proposition is true, or can be verified, on the ground that you have verified it,
that is, that you possess a verification of it. Therefore, ? being defined
by the stipulation that there is nothing that counts as a verification of
it, there is no introduction rule for falsehood.

52 per martin-l"of

?-elimination. ? true

C true
Here, in analogy with the rule of disjunction elimination, C is presupposed to be a proposition, not outright, but merely under the assumption that ? is true. This is the only divergence from Gentzen's
formulation of ex falso quodlibet.

Explanation. When you infer by this rule, you undertake to verify
the proposition C when you are provided with a proof that ? is true,
that is, by the definition of truth, with a method of verifying ?. But
this is something that you can safely undertake, because, by the definition of falsehood, there is nothing that counts as a verification of ?.
Hence ? is false, that is, cannot be verified, and hence it is impossible
that you ever be provided with a proof that ? is true. Observe the
step here from the falsity of the proposition ? to the unprovability of
the judgement that ? is true. The undertaking that you make when
you infer by the rule of falsehood elimination is therefore like saying,

I shall eat up my hat if you do such and such,
where such and such is something of which you know, that is, are
certain, that it cannot be done.

Observe that the justification of the elimination rule for falsehood
only rests on the knowledge that ? is false. Thus, if A is a proposition,
not necessarily ?, and C is a proposition provided that A is true, then
the inference A true

C true
is valid as soon as A is false. Choosing C to be ?, we can conclude, by
implication introduction, that A oe ? is true provided that A is false.
Conversely, if A oe ? is true and A is true, then, by modus ponens, ?
would be true, which it is not. Hence A is false if A oe ? is true. These
two facts together justify the nominal definition of ,A, the negation of
A, as A oe ?, which is commonly made in intuitionistic logic. However,
the fact that A is false if and only if ,A is true should not tempt one
to define the notion of denial by saying that

A is false
means that

,A is true.

on the meanings of the logical constants 53
That the proposition A is false still means that it is impossible to verify
A, and this is a notion which cannot be reduced to the notions of negation, negation of propositions, that is, and truth. Denial comes before
negation in the order of conceptual priority, just as logical consequence
comes before implication, and the kind of generality which a judgement
may have comes before universal quantification.

As has been implicit in what I have just said,

A is false = A is not true = A is not verifiable
= A cannot be verified.

Moreover, in the course of justifying the rule of falsehood elimination,
I proved that ? is false, that is, that ? is not true. Now, remember
that, in the very beginning of this lecture, we convinced ourselves that a
proposition is true if and only if the judgement that it is true is provable.
Hence, negating both members, a proposition is false if and only if the
judgement that it is true cannot be proved, that is, is unprovable. Using
this in one direction, we can conclude, from the already established
falsity of ?, that the judgement that ? is true is unprovable. This is,
if you want, an absolute consistency proof: it is a proof of consistency
with respect to the unlimited notion of provability, or knowability, that
pervades these lectures. And

(? is true) is unprovable
is the judgement which expresses the absolute consistency, if I may call
it so. By my chain of explanations, I hope that I have succeeded in
making it evident.

The absolute consistency brings with it as a consequence the relative consistency of any system of correct, or valid, inference rules.
Suppose namely that you have a certain formal system, a system of
inference rules, and that you have a formal proof in that system of the
judgement that ? is true. Because of the absolute consistency, that is,
the unprovability of the judgement that ? is true, that formal proof, although formally correct, is no proof, not a real proof, that is. How can
that come about? Since a formal proof is a chain of formally immediate
inferences, that is, instances of the inference rules of the system, that
can only come about as a result of there being some rule of inference
which is incorrect. Thus, if you have a formal system, and you have
convinced yourself of the correctness of the inference rules that belong
to it, then you are sure that the judgement that ? is true cannot be
proved in the system. This means that the consistency problem is really the problem of the correctness of the rules of inference, and that, at
some stage or another, you cannot avoid having to convince yourself

54 per martin-l"of
of their correctness. Of course if you take any old formal system, it
may be that you can carry out a metamathematical consistency proof
for it, but that consistency proof will rely on the intuitive correctness
of the principles of reasoning that you use in that proof, which means
that you are nevertheless relying on the correctness of certain forms
of inference. Thus the consistency problem is really the problem of
the correctness of the rules of inference that you follow, consciously or
unconsciously, in your reasoning.

After this digression on consistency, we must return to the semantical explanations of the rules of inference. The ones that remain are
the quantifier rules.

8-formation.

A(x) prop

(8x)A(x) prop
Explanation. The premise of this rule is a judgement which has
generality in it. If I were to make it explicit, I would have to write it

jx A(x) prop:
It is a judgement which has generality in it, although it is free from
hypotheses. And remember what it is to know such a judgement: it is
to possess a free variable proof of it. Now, assume that you do know
the premise of this rule, that is, that you possess a free variable proof
of the judgement that A(x) is a proposition. On that assumption, I
explain the conclusion to you by stipulating that a verification of the
proposition (8x)A(x) consists of a free variable proof that A(x) is true,
graphically, ..

.

A(x) true

By definition, that is a proof in which the variable x may be replaced
by anything you want, that is, any expression you want of the same
arity as the variable x. Thus, if x is a variable ranging over complete
expressions, then you must substitute a complete expression for it, and,
similarly, if it ranges over incomplete expressions of some arity. In the
Kolmogorov interpretation, the explanation of the meaning of the universal quantifier would be phrased by saying that (8x)A(x) expresses
the problem of constructing a general method of solving the problem
A(x) for arbitrary x.

8-introduction. A(x) true

(8x)A(x) true

on the meanings of the logical constants 55
Here the premise of the formation rule, to the effect that A(x) is a
proposition for arbitrary x, is still in force.

Explanation. Again, the premise of this rule is a general judgement,
which would read

jx A(x) true

if I were to employ the systematic notation that I introduced earlier
in this lecture. Now, assume that you know this, that is, assume that
you possess a free variable proof of the judgement that A(x) is true.
Then, by the principle that, if something has been done, then it can
be done, you certainly can give such a proof, and this is precisely what
you must be able, or know how, to do in order to have the right to infer
the conclusion of the rule.

8-elimination. (8x)A(x) true

A(a) true
Here it is presupposed, of course, that A(x) is a proposition for arbitrary x. And, as you see, I have again chosen the usual formulation
of the elimination rule for the universal quantifier rather than the one
which is patterned upon the elimination rules for falsehood, disjunction, and existence.

Explanation. First of all, observe that, because of the tacit assumption that A(x) is a proposition for arbitrary x, both (8x)A(x) and A(a)
are propositions, where a is an expression of the same arity as the variable x. Now, assume that you know the premise, that is, that you know
how to verify the proposition (8x)A(x), and I shall explain to you how
to verify the proposition A(a). To begin with, put your knowledge of
the premise into practice. That will give you a verification of (8x)A(x),
which, by the definition of the universal quantifier, is a free variable
proof that A(x) is true, ..

.
A(x) true

Now, this being a free variable proof means precisely that it remains a
proof whatever you substitute for x. In particular, it remains a proof
when you substitute a for x so as to get

...

A(a) true
So now you have acquired a proof that A(a) is true. By the definitions
of the notions of proof and truth, this proof is knowledge how to verify

56 per martin-l"of
the proposition A(a). Thus, putting it into practice, you end up with
a verification of A(a), as required.

9-formation.

A(x) prop

(9x)A(x) prop
Explanation. Just as in the formation rule associated with the universal quantifier, the premise of this rule is really the general judgement

jx A(x) prop;
although I have not made the generality explicit in the formulation of
the rule. Assume that you know the premise, that is, assume that you
possess a free variable proof

...

A(x) prop
guaranteeing that A(x) is a proposition, and I shall explain to you what
proposition (9x)A(x) is, that is, what counts as a verification of it. The
explanation is that a verification of (9x)A(x) consists of an expression
a of the same arity as the variable x and a proof

...

A(a) true
showing that the proposition A(a) is true. Observe that the knowledge
of the premise is needed in order to guarantee that A(a) is a proposition,
so that it makes sense to talk about a proof that A(a) is true. In
the Kolmogorov interpretation, (9x)A(x) would be explained as the
problem of finding an expression a, of the same arity as the variable x,
and a method of solving the problem A(a).

9-introduction. A(a) true

(9x)A(x) true
Here, as usual, the premise of the formation rule is still in force, which
is to say that A(x) is assumed to be a proposition for arbitrary x.

Explanation. Assume that you know the premise, that is, assume
that you possess a proof that A(a) is true,

...

A(a) true

on the meanings of the logical constants 57
By the preceding explanation of the meaning of the existential quantifier, the expression a together with this proof make up a verification of
the proposition (9x)A(x). And, possessing a verification of the proposition (9x)A(x), you certainly know how to verify it, which is what you
must know in order to have the right to conclude that (9x)A(x) is true.
Like in my explanations of all the other introduction rules, I have here
taken for granted the principle that, if something has been done, then
it can be done.

9-elimination.

(9x)A(x) true

(A(x) true)

C true
C true

Here it is presupposed, not only that A(x) is a proposition for arbitrary
x, like in the introduction rule, but also that C is a proposition provided
that the proposition (9x)A(x) is true.

Explanation. First of all, in order to make it look familiar, I have
written the second premise in Gentzen's notation

(A(x) true)

C true
rather than in the notation

A(x) true jx C true;
but there is no difference whatever in sense. Thus the second premise
is really a hypothetico-general judgement. Now, assume that you know
the premises. By the definition of the notion of truth, your knowledge of
the first premise is knowledge how to verify the proposition (9x)A(x).
Put that knowledge of yours into practice. You then end up with
a verification of the proposition (9x)A(x). By the definition of the
existential quantifier, this verification consists of an expression a of the
same arity as the variable x and a proof that the proposition A(a) is
true, ..

.
A(a) true

Now use your knowledge, or proof, of the second premise. Because of
the meaning of a hypothetico-general judgement, this proof

A(x) true.

..

C true

58 per martin-l"of
is a free variable proof that C is true from the hypothesis that A(x)
is true. Being a free variable proof means that you may substitute
anything you want, in particular, the expression a, for the variable x.
You then get a hypothetical proof

A(a) true.

..

C true

that C is true from the hypothesis that A(a) is true. Supplementing this
hypothetical proof with the proof that A(a) is true that you obtained
as a result of putting your knowledge of the first premise into practice,
you get a proof ..

.

A(a) true.

..

C true

that C is true, and this proof is nothing but knowledge how to verify
the proposition C. Thus, putting it into practice, you end up having
verified the proposition C, as required.

The promise of the title of these lectures, On the Meanings of the
Logical Constants and the Justifications of the Logical Laws, has now
been fulfilled. As you have seen, the explanations of the meanings of
the logical constants are precisely the explanations belonging to the
formation rules. And the justifications of the logical laws are the explanations belonging to the introduction and elimination rules, which
are the rules that we normally call rules of inference. For lack of time,
I have only been able to deal with the pure logic in my semantical explanations. To develop some interesting parts of mathematics, you also
need axioms for ordinary inductive definitions, in particular, axioms of
computation and axioms for the natural numbers. And, if you need
predicates defined by transfinite, or generalized, induction, then you
will have to add the appropriate formation, introduction, and elimination rules for them.

I have already explained how you see the consistency of a formal
system of correct inference rules, that is, the impossibility of constructing a proof ..

.
? true

that falsehood is true which proceeds according to those rules, not by
studying metamathematically the proof figures divested of all sense, as

on the meanings of the logical constants 59
was Hilbert's program, but by doing just the opposite: not divesting
them of sense, but endowing them with sense. Similarly, suppose that
you have a proof ..

.
A true

that a proposition A is true which depends, neither on any assumptions,
nor on any free variables. By the definition of truth and the identification of proof and knowledge, such a proof is nothing but knowledge how
to verify the proposition A. And, as I remarked earlier in this lecture,
verifying the proposition A by putting that knowledge into practice is
the same as reducing the proof to introductory form and deleting the
last, introductory inference. Moreover, the way of reducing the proof
which corresponds to the semantical explanations, notably of the elimination rules, is precisely the way that I utilized for the first time in
my paper on iterated inductive definitions in the Proceedings of the
Second Scandinavian Logic Symposium, although merely because of
its naturalness, not for any genuine semantical reasons, at that time.
But no longer do we need to prove anything, that is, no longer do we
need to prove metamathematically that the proof figures, divested of
sense, reduce to introductory form. Instead of proving it, we endow
the proof figures with sense, and then we see it! Thus the definition
of convertibility, or computability, and the proof of normalization have
been transposed into genuine semantical explanations which allow you
to see this, just as you can see consistency semantically. And this is
the point that I had intended to reach in these lectures.

60 per martin-l"of

Postscript, Feb. 1996
The preceding three lectures were originally published in the Atti
degli Incontri di Logica Matematica, Vol. 2, Scuola di Specializzazione
in Logica Matematica, Dipartimento di Matematica, Universit`a di
Siena, 1985, pp. 203-281. Since they have been difficult to obtain,
and are now even out of print, they are reprinted here by kind permission of the Dipartimento di Matematica, Universit`a di Siena. Only
typing errors have been corrected. The reader who wishes to follow
the further development of the ideas that were brought up for the first
time in these lectures is referred to the papers listed below.

Per Martin-L"of (1987) Truth of a proposition, evidence of a judgement,

validity of a proof. Synthese, 73, pp. 407-420.

---- (1991) A path from logic to metaphysics. In Atti del Congresso

Nuovi Problemi della Logica e della Filosofia della Scienza, Viareggio, 8-13 gennaio 1990, Vol. II, pp. 141-149. CLUEB, Bologna.

---- (1994) Analytic and synthetic judgements in type theory. In

Paolo Parrini (ed.), Kant and Contemporary Epistemology, pp. 87-
99. Kluwer Academic Publishers, Dordrecht/Boston/London.

---- (1995) Verificationism then and now. In W. DePauli-Schimanovich,

E. K"ohler, and F. Stadler (eds.), The Foundational Debate: Complexity and Constructivity in Mathematics and Physics, pp. 187-
196. Kluwer Academic Publishers, Dordrecht/Boston/London.

---- (1996) Truth and knowability: on the principles C and K of

Michael Dummett. In H. G. Dales and G. Oliveri (eds.), Truth
in Mathematics. Clarendon Press, Oxford. Forthcoming.

Department of Mathematics
University of Stockholm
Sweden

-}

-- record  -- WORKS with this additional token
