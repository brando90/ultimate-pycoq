from pathlib import Path

COQ_PROJECT_ROOT = Path('~/proverbot9001/coq-projects/').expanduser()

# glob all project dirs
project_dirs = list(COQ_PROJECT_ROOT.glob('*'))

print(f'--- {len(project_dirs)} projects in total ---')
for each in project_dirs:
    print(each.name)
    
    coq_scripts = each.glob('*.v')

    for each_script in coq_scripts:
        print(f'    {each_script.name}')
