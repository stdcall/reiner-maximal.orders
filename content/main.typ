#set document(
  title: "Maximal Orders",
  author: "Irving Reiner",
  date: none,
)
#import "book-style.typ": book-style
#import "frontmatter/cover.typ": cover
#cover()
#show: book-style
#set page(numbering: "i")
#counter(page).update(2)
#import "frontmatter/series.typ": series-page
#series-page()
#import "frontmatter/title.typ": title-page
#title-page()
#include "00-preface.typ"
#include "00-acknowledgements.typ"
#heading(level: 1, numbering: none, outlined: false)[Contents]
#outline(title: none, depth: 2)
#include "frontmatter/notation.typ"
#set page(numbering: "1")
#counter(page).update(1)
#include "01-00-algebraic-preliminaries.typ"
#import "numbering.typ": continue-sections
#continue-sections()
#include "01-01-integral-closure.typ"
#include "01-02-homological-algebra.typ"
#include "01-03-localization.typ"
#include "01-04-dedekind-domains.typ"
#include "01-05-completions-and-valuations.typ"
#include "01-06-radicals-of-rings.typ"
#include "01-07-semisimple-rings.typ"
#include "02-00-orders.typ"
#continue-sections()
#include "02-08-orders-definitions-and-examples.typ"
#include "02-09-reduced-norms-and-traces.typ"
#include "02-10-existence-of-maximal-orders.typ"
#include "02-11-localization-of-orders.typ"
#include "03-00-maximal-orders-in-skewfields.typ"
#continue-sections()
#include "03-12-uniqueness-of-maximal-orders.typ"
#include "03-13-ramification-index-inertial-degree.typ"
#include "03-14-finite-residue-class-field.typ"
#include "04-00-morita-equivalence.typ"
#continue-sections()
#include "04-15-progenerators.typ"
#include "04-16-morita-correspondence.typ"
#include "05-00-maximal-orders-over-dvr.typ"
#continue-sections()
#include "05-17-maximal-orders-complete-local-case.typ"
#include "05-18-maximal-orders-local-case.typ"
#include "05-19-ideals.typ"
#include "05-20-different-discriminant.typ"
#include "06-00-maximal-orders-over-dedekind-domains.typ"
#continue-sections()
#include "06-21-basic-results.typ"
#include "06-22-ideal-theory.typ"
#include "06-23-alternate-global-ideal-theory.typ"
#include "06-24-norms-of-ideals.typ"
#include "06-25-different-discriminant-global.typ"
#include "06-26-ideal-classes.typ"
#include "06-27-genus.typ"
#include "07-00-crossed-product-algebras.typ"
#continue-sections()
#include "07-28-brauer-groups.typ"
#include "07-29-crossed-product-algebras.typ"
#include "07-30-cyclic-algebras.typ"
#include "07-31-cyclic-algebras-local.typ"
#include "08-00-simple-algebras-over-global-fields.typ"
#continue-sections()
#include "08-32-splitting-of-simple-algebras.typ"
#include "08-33-reduced-norms-global.typ"
#include "08-34-eichler-theorem.typ"
#include "08-35-ideal-class-groups.typ"
#include "08-36-k0-of-maximal-orders.typ"
#include "08-37-picard-groups.typ"
#include "08-38-non-maximal-orders.typ"
#include "09-00-hereditary-orders.typ"
#continue-sections()
#include "09-39-hereditary-orders-local.typ"
#include "09-40-hereditary-orders-global.typ"
#include "09-41-group-rings.typ"
#include "80-bibliography.typ"
#include "90-index.typ"
