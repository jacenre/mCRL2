set(MCRL2_TOOLS
  besconvert  
  lps2pres
  lpscleave
  lpscombine
  lpsrealelm
  lpssymbolicbisim
  lts2pres
  ltscombine
  pbes2cvc4
  pbes2yices
  pbesabsinthe
  pbesbackelm
  pbesiteration
  pbespareqelm
  pbespor
  pbespathreduction
  pbessymbolicbisim
  presconstelm
  presinfo
  presinst
  presparelm
  prespp
  presrewr
  pressolve
  symbolic_exploration
  respp
  resinfo
  txt2pres
  txt2res
)

if(MCRL2_ENABLE_EXPERIMENTAL)
  foreach(TOOL ${MCRL2_TOOLS})
    add_subdirectory(${TOOL})
  endforeach()
endif()
