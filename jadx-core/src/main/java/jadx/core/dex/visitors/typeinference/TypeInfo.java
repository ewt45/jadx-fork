package jadx.core.dex.visitors.typeinference;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import org.jetbrains.annotations.NotNull;

import jadx.core.dex.instructions.args.ArgType;
import jadx.core.dex.instructions.args.CodeVar;

public class TypeInfo {
	private ArgType type = ArgType.UNKNOWN;

	private final Set<ITypeBound> bounds = new LinkedHashSet<>();

	@NotNull
	public ArgType getType() {
		return type;
	}

	public List<String> addedPlaces = new ArrayList<>();
	public void setType(ArgType type) {
		this.type = type;
		CodeVar.addStrace(addedPlaces, "类型设置为"+type);
	}

	public Set<ITypeBound> getBounds() {
		return bounds;
	}

	@Override
	public String toString() {
		return "TypeInfo{type=" + type + ", bounds=" + bounds + '}';
	}
}
