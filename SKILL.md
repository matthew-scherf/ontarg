---
name: human-voice-writing
description: Write prose in a natural human voice, free of the patterns that make text read as machine-generated — uniform sentence rhythm, reflexive hedging, corporate vocabulary (delve, leverage, tapestry, robust), negative parallelism ("it's not X, it's Y"), and vague filler. Use this skill whenever the user asks to write, draft, rewrite, edit, humanize, or "de-robotify" any prose — articles, essays, blog posts, emails, reports, marketing or web copy, cover letters, social posts, scripts, or fiction. Apply it by default to prose-writing tasks even when the user doesn't say the words "AI", "voice", or "human" — unless they explicitly ask for a deliberately formal, templated, or boilerplate style.
---

# Human Voice Writing

The goal is prose a specific person would actually write and that a reader wants to finish. Not "text that beats a detector." That distinction matters: AI-detection tools are noisy (false-positive rates run high, especially on formal or non-native English), so chasing a score is a losing game. But the same habits that trip detectors also make writing dull, evasive, and forgettable to human readers. Fix the writing and the score takes care of itself.

This skill is about genuine craft, not disguise. Do not use it to help someone misrepresent authorship where that matters (e.g. passing off work as their own in a context that forbids it). Everywhere else — writing better, editing a rough draft, giving flat prose a pulse — it applies freely.

## Why machine text reads as machine text

Understanding the cause lets you fix it at the root instead of find-and-replacing symptoms:

- **Low perplexity.** Language models pick the highest-probability next word, so the prose is smooth and predictable. Every choice is the safe, expected one. Humans reach for the apt-but-surprising word.
- **Low burstiness.** Models emit sentences of similar length and shape — tidy rectangles. Human rhythm is uneven: a long winding clause, then a short one. Then a fragment.
- **Median-safe hedging.** Training rewards inoffensive, both-sides, take-no-position output. The result commits to nothing and says "it depends."

So the three real fixes are: make word choices that are precise rather than generic, vary rhythm deliberately, and commit to actual claims. The word lists below are downstream of these.

## The kill list

None of these words is banned. The tell is **density and reflex** — a paragraph that stacks five of them, or an em-dash reaching for a grander register every third sentence. One "crucial" is fine. The problem is when they're the default. When you catch one, don't swap in a fancier synonym; say the concrete thing the word was standing in for.

**Inflated verbs** — delve → dig into / look at · leverage → use · foster → build · harness → use · underscore → show · embark → start · unveil → show / launch · unlock → open up · elevate → improve · revolutionize → change · empower → let (someone) · navigate → handle / work through · showcase → show · streamline → simplify

**Hollow adjectives** — seamless, robust, cutting-edge, crucial, pivotal, dynamic, multifaceted, comprehensive, innovative, versatile, vibrant, meticulous. Fix: replace with the actual spec or detail. Not "robust pipeline" but "a pipeline that handles 10k requests/sec."

**Spatial metaphors** (the loudest tell) — landscape, realm, tapestry, ecosystem, beacon, symphony, testament, journey. Fix: name the thing the metaphor is hiding. "A rich tapestry of signals" → "six different signals."

**Throat-clearing and glue** — "It's important to note that", "It's worth mentioning", "In today's rapidly evolving [X]", "In the world of", "When it comes to", "Furthermore / Moreover" opening sentence after sentence, "In conclusion", "In essence", "Ultimately". Fix: usually just delete and state the thing. Swap furthermore/moreover for plain "And," "Also," "Plus," or nothing.

**Reflexive openers** — "Certainly!", "Great question", "Let's dive in", "Buckle up". Just start.

## Structural tells to avoid

These are subtler than vocabulary and are what experienced readers actually catch.

- **Negative parallelism** — "It's not about X, it's about Y" / "not just X, but Y" / "This doesn't just save time, it transforms your workflow." Fine *once*, when the second half adds real information. The tell is the performed version where both halves are the same claim in fancier costume. Test: delete the first clause; if nothing is lost, it was decoration. Cut it.
- **Escalating rule-of-three** — "It saves time, cuts errors, and redefines what's possible." The first two items are concrete; the third inflates into grandeur. Keep lists honest; don't let the third item reach.
- **"No X. No Y. Just Z."** slogan cadence. Effective in one headline, exhausting as a default section-closer.
- **Rhetorical-question transitions** — "The result? A 40% drop." Real writers do this occasionally; AI does it every 150 words. Ration it.
- **The em-dash pivot** — stopping a sentence mid-thought to relaunch at a loftier register. (Em-dashes themselves are fine — this specific move is the tell.)
- **Perfect-rectangle paragraphs** — three or four sentences, all 15–20 words, all subject-verb-object, no fragment, no aside, no variation. Break them.
- **The opinion vacuum** — "both approaches have merit," "it could be argued," "ultimately it depends on your situation." This is the most damaging one. Take a position. If you genuinely can't, say what you'd bet on if forced.
- **Press-release tone** — describing people, products, or places in uniformly positive, important-sounding language while omitting specific, odd, or unflattering facts. The specific fact ("filed the patent from a garage in 1987") is always more human than the generic praise ("a visionary pioneer").

## What to do instead

- **Vary rhythm on purpose.** After a long sentence, write a short one. Occasionally a fragment. Read it aloud — if your breathing never changes across three paragraphs, the rhythm is too even.
- **Use a real voice.** Contractions (it's, don't, you're). Start sentences with And / But / So where it flows. First person where it fits ("I'd avoid this").
- **Be specific.** Concrete nouns over abstractions. Real numbers, dates, and names over "recent studies," "many experts," "a leading company." If you don't have the real figure, describe what you actually observed instead of inventing a stat.
- **Commit.** Say the true thing plainly. Positions, not hedges.
- **Add texture.** One concrete detail, aside, or dry observation carries more than a paragraph of smooth generality. Dry beats punny.
- **Cut ruthlessly.** Most throat-clearing sentences can be deleted whole with zero loss.

**Before:** "In today's rapidly evolving digital landscape, leveraging robust analytics tools is crucial for businesses seeking to unlock seamless growth."
**After:** "Analytics won't grow your business by themselves, but you can't fix what you can't see. Start by tracking three numbers: signups, churn, and revenue per user."

## Self-edit pass

Before delivering any prose, run through it once:

1. **Kill-list scan** — hunt the inflated verbs, hollow adjectives, and spatial metaphors. Replace each with the concrete thing, or cut it.
2. **Rhythm check** — find any run of three-plus same-length sentences and break it (add a fragment, merge two, split one).
3. **Hedge hunt** — find every "it depends," "both sides," "it's important to note." Delete or replace with a real position.
4. **Specificity pass** — turn vague nouns into named, numbered, dated specifics wherever you legitimately can.
5. **Read aloud** — anything you'd never say out loud to a colleague, rewrite.

## Don't overcorrect

Overcorrection is its own fingerprint. Watch for it:

- Every sentence a fragment, a joke every line, forced slang, or an em-dash in every paragraph is just a *different* tic, equally detectable and more annoying.
- **Match register to context.** A legal memo, scientific abstract, or safety notice legitimately has low burstiness and formal vocabulary — jamming personality in there is wrong. Human voice means *appropriate* voice, not maximum quirk.
- The target is always the same: writing that sounds like a real, specific person wrote it for a real reader. If a change doesn't serve that, skip it.
