namespace archieve
def lerArquivo (caminho: String) : IO (Array String) := do
  -- Tenta abrir o arquivo no caminho especificado
  let handle ← IO.FS.Handle.mk caminho IO.FS.Mode.read
  -- Lê todo o conteúdo do arquivo
  let conteudo ← handle.readToEnd
  -- Divide o conteúdo em linhas, usando '\n' como delimitador
  let linhas := conteudo.splitOn "\n"
  -- Retorna as linhas como uma lista
  return linhas.toArray

-- Função principal (a arrumar)
def main : IO Unit := do
  let caminho := "aux.txt"  -- Caminho do arquivo a ser lido
  let linhas ← lerArquivo caminho

  for linha in linhas do
    IO.println linha
end archieve
