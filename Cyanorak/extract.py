import re
import sys
import getopt


######################
####     MAIN     ####
######################

if __name__ == "__main__":
  try :
    opts, args = getopt.getopt(sys.argv[1:], "hs:",["file="])
  except getopt.GetoptError:
    sys.exit()
  file = None
  for opt,arg in opts:
    if(opt == "--file"):
      file = arg
  f = open(file, 'r')

  # Header lines
  line = f.readline()
  line = f.readline()

  # Genome size (total of nucleotides)
  genome_start, genome_end = [int(i) for i in f.readline().split('\t')[3:5]]
  # Marks used to compute the sizes of the intergenic regions
  marks = [genome_start]
  # List of genes
  genes = []
  # List for the genes orientation
  strands = []

  line = f.readline()
  while line:
    _, _, _, start, end, _, strand, _, attributes = line.split('\t')

    pattern = re.compile('cluster_number=CK_([0-9]+)')
    matches = pattern.findall(attributes)
    # If there is no ID for the gene, it is ignored
    if len(matches):
      id = int(matches[0])
      # The first copy of each gene is mapped
      if id not in genes:
        genes.append(id)
        strands.append(int(strand + '1'))
        marks.append(int(start))
        marks.append(int(end))

    line = f.readline()
  f.close()

  # Computing the sizes of the intergenic regions
  marks.append(genome_end)
  intergenic_regions = []
  for i in range(1, len(marks), 2):
    intergenic_regions.append(max(marks[i] - marks[i - 1], 0))

  # Assigning the gene orientation
  for i in range(len(genes)):
    genes[i] *= strands[i]

  # Checking the number of genes and intergenic regions
  if (len(genes) + 1)  != len(intergenic_regions):
    raise ValueError('It was detected an incompatible number of genes and intergenic regions.')

  print(str(genes).replace(' ',''), str(intergenic_regions).replace(' ',''))