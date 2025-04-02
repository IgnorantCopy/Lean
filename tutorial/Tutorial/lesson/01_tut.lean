structure Poem where
  isInteresting : Bool
  isPopular : Bool
  isModern : Bool
  isAffected : Bool
  isYourPoem : Bool
  hasSoapBubbleTheme : Bool

-- Axiom 1: No interesting poems are unpopular among people of real taste.
axiom interesting_implies_popular : ∀ (p : Poem), p.isInteresting →  p.isPopular

-- Axiom 2: No modern poetry is free from affectation.
axiom modern_implies_affected : ∀ (p : Poem), p.isModern →  p.isAffected

-- Axiom 3: All your poems are on the subject of soap bubbles.
axiom your_poem_implies_soap_bubble_theme : ∀ (p : Poem), p.isYourPoem →  p.hasSoapBubbleTheme

-- Axiom 4: No affected poetry is popular among people of real taste.
axiom affected_implies_not_popular : ∀ (p : Poem), p.isAffected →  ¬ p.isPopular

-- Axiom 5: Only a modern poem would be on the subject of soap bubbles.
axiom soap_bubble_theme_implies_modern : ∀ (p : Poem), p.hasSoapBubbleTheme →  p.isModern

-- Theorem to be approved: Therefore none of your poems are interesting.
theorem none_your_poems_interesting : ∀ (p : Poem), p.isYourPoem →  ¬ p.isInteresting := by
  intro p your_poem
  have h_soap : p.hasSoapBubbleTheme := your_poem_implies_soap_bubble_theme p your_poem
  have h_modern : p.isModern := soap_bubble_theme_implies_modern p h_soap
  have h_affected : p.isAffected := modern_implies_affected p h_modern
  have h_not_pop : ¬ p.isPopular := affected_implies_not_popular p h_affected
  apply mt (interesting_implies_popular p) h_not_pop
