import sys
import getopt


######################
####     MAIN     ####
######################

if __name__ == "__main__":
  try :
    opts, args = getopt.getopt(sys.argv[1:], "hs:",["source=", "target="])
  except getopt.GetoptError:
    sys.exit()
  source_filename = None
  target_filename = None
  for opt,arg in opts:
    if(opt == "--source"):
      source_filename = arg
    if(opt == "--target"):
      target_filename = arg

  # Reading the extracted files
  f = open(source_filename, 'r')
  source_genes, source_ir = [eval(i) for i in f.readline().split()]
  f.close()
  f = open(target_filename, 'r')
  target_genes, target_ir = [eval(i) for i in f.readline().split()]
  f.close()

  # Mapping the target genome as the identity permutation (not reduced yet)
  map = {}
  index = 1
  for i in range(len(target_genes)):
    map[target_genes[i]] = index
    target_genes[i] = index
    index += 1

  # Mapping the source genome according to the target
  # If a gene is not present in the target genome the value zero is assigned (indicating that must be removed).
  for i in range(len(source_genes)):
    if source_genes[i] in map.keys():
      source_genes[i] = map[source_genes[i]]
    elif -source_genes[i] in map.keys():
      source_genes[i] = -map[-source_genes[i]]
    else:
      source_genes[i] = 0

  # Computing the breakpoints, it will be used to reduce the source genome (mapping conserved conserved blocks into a gene)
  breaks = []
  for i in range(len(source_genes) - 1):
    if (source_genes[i + 1] - source_genes[i]) not in [0,1]:
      breaks.append(i + 1)
  breaks = [0] + breaks + [len(source_genes)]
  blocks = []

  # Reducing process of the source genome
  pi = []
  pi_ir = [source_ir[0]]
  for i in range(len(breaks) - 1):
    if source_genes[breaks[i]] < 0:
      pi.append(source_genes[breaks[i]])
      b = [abs(g) for g in source_genes[breaks[i]:breaks[i + 1]]]
      b.reverse()
      blocks.append(b)
    else:
      pi.append(source_genes[breaks[i + 1] - 1])
      b = source_genes[breaks[i]:breaks[i + 1]]
      blocks.append(b)
    pi_ir.append(source_ir[breaks[i + 1]])

  # The blocks are used to reduce the target genome
  blocks = sorted([i for i in blocks if sum(i) != 0])
  aux = []
  for i in range(len(blocks) - 1):
    if min(blocks[i + 1]) - max(blocks[i]) != 1:
      aux.append(list(range(max(blocks[i]) + 1, min(blocks[i + 1]))))
  blocks = sorted(blocks + aux)

  # Reducing process of the target genome
  iota = []
  iota_ir = [target_ir[0]]
  for b in blocks:
    i = max(b)
    iota.append(i)
    iota_ir.append(target_ir[i])

  # Mapping the target genome as the identity permutation (reduced instance)
  map = {}
  index = 1
  for i in range(len(iota)):
    map[iota[i]] = index
    iota[i] = index
    index += 1

  # Mapping the source genome according to the target
  for i in range(len(pi)):
    if pi[i] in map.keys():
      pi[i] = map[pi[i]]
    elif -pi[i] in map.keys():
      pi[i] = -map[-pi[i]]
    else:
      pi[i] = 0

  # Output
  print(str(pi).replace(' ',''), str(pi_ir).replace(' ',''), str(iota_ir).replace(' ',''))
  # print(str(iota).replace(' ',''), str(iota_ir).replace(' ',''))