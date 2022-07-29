import re
import io


file_to_process = 'README.md'

regex_for_lines = r'<!-- Process: {(.*)} -->'
regex_for_evaluations = r'(.*?)@@(.*)@@(.*)'

encoding_of_content = 'utf8'
url_base = 'https://github.com/gilesgshaw/UA-Lean/blob/working/'



def line_of(phrase, file):
    with open(file, encoding=encoding_of_content) as content:
        for num, line in enumerate(content, 1):
            if phrase in line:
                return num

def url_of(phrase, file):
    return url_base + file + '#L' + str(line_of(phrase, file))

def eval(input):
    regex_two_arguments = r'\(\'(.*)\',[ ]?\'(.*)\''
    m = re.search('url_of' + regex_two_arguments, input)
    if m is not None:
        return url_of(m.group(1), m.group(2))
    return input

def process(str):
    m = re.search(regex_for_evaluations, str)
    while m is not None:
        str = m.group(1) + eval(m.group(2)) + m.group(3)
        m = re.search(regex_for_evaluations, str)
    return str



with io.open(file_to_process, 'r', newline='\n') as f:
    content = f.read()

with io.open(file_to_process, 'w', newline='\n') as f:
    line_pending = False
    pending_line = ""
    for line in content.splitlines():
        if line_pending:
            f.write(pending_line + '\n')
            line_pending = False
        else:
            f.write(line + '\n')
            m = re.search(regex_for_lines, line)
            if m is not None:
                line_pending = True
                pending_line = process(m.group(1))
