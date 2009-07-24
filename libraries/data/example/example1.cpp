#include <cassert>
#include "mcrl2/data/data_expression.h"
#include "mcrl2/data/standard_utility.h"
#include "mcrl2/atermpp/aterm_init.h"

using namespace mcrl2::data;

int main(int argc, char* argv[])
{
  MCRL2_ATERMPP_INIT(argc, argv)

  data_expression two   = sort_nat::nat(2);
  data_expression three = sort_nat::nat(3);
  data_expression five  = sort_nat::plus(two, three);

  assert(five.sort() == sort_nat::nat());
  return 0;
}
