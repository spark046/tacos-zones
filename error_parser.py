from io import TextIOWrapper
import sys

debug = False

def rfind_nth_overlapping(string: str, substring: str, n: int):
	start = string.rfind(substring)
	while start >= 0 and n > 1:
		start = string.rfind(substring, 0, len(string) - (start+1))
		n -= 1
	return start

#e.g. <hello<wow>>byebye! becomes hellow<wow>
def get_word_inside_bracket(string: str):
	bracket_count = 1
	word = ""

	#if(string.count('<') != string.count('>')):
	#	print("ERROR: Angle Bracket count is unbalanced")
	#	print(string)

	if(string.startswith('<')):
		for char in string[1:]:
			if(char == '<'):
				bracket_count += 1
			elif(char == '>'):
				bracket_count -= 1

			if(bracket_count == 0):
				break

			word += char
	else:
		print("ERROR: Word doesn't start with \'<\'")
	
	return word

#Word needs <> brackets!
def length_of_first_word(string : str):
	length = 0
	
	bracket_count = 0
	first_bracket_seen = False

	for char in string:
		length += 1

		if(char == '<'):
			first_bracket_seen = True
			bracket_count += 1
		elif(char == '>'):
			bracket_count -=1

		if(bracket_count == 0 and first_bracket_seen):
			break

	return length

# std::vector<std::set< V >> D
# CanonicalWord< V > D
def parse_canonical_word(text: str):
	if(text.startswith("std::vector<std::set<")):
		return "CanonicalWord<" +  (parse_variant(get_word_inside_bracket(text[len("std::vector<std::set"):])) + ">" +
									parse_default(text[len("std::vector<std::set") + len(get_word_inside_bracket(text[len("std::vector<std::set"):])) + 3 :]))
	else:
		print("INVALID WORD: CanonicalWord wrong\n" + text)
		return ""

# * PlantRegionState< P > * ATARegionState< A > *
# P, A
def parse_variant(text: str):
	plant_index = text.find("PlantRegionState<")
	ata_index = text.find("ATARegionState<")

	if(plant_index != -1 and ata_index != 1):
		text = parse_plant(text[plant_index:]) + ", " + parse_ata(text[ata_index:])
	else:
		print("INVALID WORD: Variant wrong\n" + text)
		return ""
	
	return text

# PlantRegionState< D > *
# D
def parse_plant(text: str):
	if(text.startswith("PlantRegionState<") and '>' in text):
		return parse_default(get_word_inside_bracket(text[len("PlantRegionState"):]))
	else:
		print("INVALID WORD: PlantRegionState wrong\n" + text)
		return ""

# ATARegionState< D > *
# D
def parse_ata(text: str):
	if(text.startswith("ATARegionState<") and '>' in text):
		return parse_default(get_word_inside_bracket(text[len("ATARegionState"):]))
	else:
		print("INVALID WORD: ATARegionState wrong\n" + text)
		return ""

# std::__cxx11::basic_string (< * > | "") (, | > | "")
# std::string
def parse_string(text: str):
	if(text.startswith("std::__cxx11::basic_string")):
		if(text[text[len("std::__cxx11::basic_string")] == '<']):
			return "std::string" + text[len("std::__cxx11::basic_string") + len(get_word_inside_bracket(text[len("std::__cxx11::basic_string"):]))+2:]
		else:
			return "std::string" + text[len("std::__cxx11::basic_string"):]

# fluent::NamedType R
# Location< R 
def parse_namedtype(text: str):
	if(text.startswith("fluent::NamedType<") and '>' in text):
		return "Location<" + parse_raw_type(text[len("fluent::NamedType"):])
	else:
		print("INVALID WORD: fluent::NamedType wrong\n" + text)
		return ""

# < D , * > D
# D > D
def parse_raw_type(text: str):
	bracket_count = 0

	output = ""

	for char in text[1:]:
		if(char == '<'):
			bracket_count += 1
		elif(char == '>'):
			bracket_count -= 1
		
		if(char == ',' and bracket_count == 0):
			return parse_default(output) + '>' + parse_default(text[len(get_word_inside_bracket(text))+2:])
		
		output += char

def parse_default(text: str):
	if(debug):
		print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n" + text)

	if(len(text) == 0):
		return ""
	
	if(text.startswith(",")):
		return "," + parse_default(text[1:])
	
	if(text.startswith(" ")):
		return " " + parse_default(text[1:])
	
	if(text.startswith(">")):
		return ">" + parse_default(text[1:])
	
	if(text.startswith("std::variant<")):
		return parse_variant(text) + parse_default(text[length_of_first_word(text)])
	
	if(text.startswith("std::vector<std::set<")):
		return parse_canonical_word(text)
	
	if(text.startswith("fluent::NamedType<")):
		return parse_namedtype(text)

	if(text.startswith("std::__cxx11::basic_string")):
		return parse_string(text)

	# D: * < D > D
	if('<' in text):
		if('>' in text):
			text = (text[0 : text.find('<')+1] + # * <
					parse_default(text[text.find('<')+1 : text.rfind('>')-1]) + # D
					'>' + # >
					parse_default(text[text.rfind('>')+1 : len(text)])) # D
		else:
			print("INVALID WORD: Open Angle Bracket Dangling\n" + text)

	return text

def recursive_descent(file: TextIOWrapper):
	text = file.readline()

	print("Processing file...")

	#if(text.count('<') != text.count('>')):
	#	print("INVALID WORD: Angle Bracket count not same")
	#	print("<: " + str(text.count('<')) + "\n>: " + str(text.count('>')))
	#	return
	
	print(parse_default(text))

def test():
	print("\nTESTING named_type\n")

	string = "fluent::NamedType<Hello<>, trash>, std::__cxx11::basic_string<shit>"

	print(parse_default(string))

def test_canonical_word():
	print("\nTESTING canonical_word\n")

	string = "std::vector<std::set<std::variant<blalspdaspjdpajspdp djsiajdosjaoidjsao PlantRegionState<LocationT> somemore shit ATARegionState<ConstraintType>dbsahdisahidhsaijdoas>>> MORE SHIT THAT SHOULD STAY"

	print(parse_default(string))

def main():
	global debug	

	args = sys.argv[1:]
	if(len(args) == 2 and args[0] == "-f"):
		file_name = args[1]
	elif(len(args) == 3 and args[0] == "-f" and args[2] == "-d"):
		file_name = args[1]
		debug = True
	else:
		print("Invalid Parameters!")
		print("Usage:")
		print("error_parser.py -f [FILENAME] (-d)")
		return
	
	file = open(file_name, "r")

	if(debug):
		test()
		test_canonical_word()

	recursive_descent(file)


if __name__ == "__main__":
	main()